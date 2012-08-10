#!/usr/bin/perl
#
# mboxgrep-perl is a very simple mbox file parser.
#
# Copyright (C) 2011 Stanislaw Findeisen <stf at eisenbits.com>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.
#
# Changes history:
#
# 2011-05-28 (STF) Initial version.

use warnings;
use strict;
use utf8;
use integer;

use constant {
    HMSGID       => 1,
    HDATE        => 2,
    HFROM        => 3,
    HSUBJECT     => 4,
    HTO          => 5,
    HCC          => 6,

    # RE_USER_EXPR => qr//

    RE_BODY_START        => qr/^[\w]*$/,
    RE_HEADER_START      => qr/^From - [\d\s\w:]*$/,
    RE_HEADER_FIELD      => qr/^([a-zA-Z-]+):(.*)$/,

    RE_MSGIDSTR_MID   => qr/^message-id$/,
    RE_MSGIDSTR_IDENT => qr/^identity$/,
    RE_MSGIDSTR_CONT  => qr/^content$/,

    C_MSGID_NONE  => 1,        # all messages considered mutually different
    C_MSGID_MID   => 2,
    C_MSGID_IDENT => 3,
    C_MSGID_CONT  => 4,

    MESSAGE_ID_DEFAULT => 0,   # when there is no Message-ID header

    VERSION      => '0.1',
    VERSION_DATE => '2011-05-28'
};

use POSIX qw(strftime locale_h);
use Encode qw(encode encode_utf8 decode decode_utf8);
use File::Copy qw(move);
use File::Temp qw(tempfile);
use Getopt::Long;
use Digest::MD5 qw(md5);
use Digest::SHA qw(sha256);

####################################
# Global variables
####################################

my $quiet2  = 0;

####################################
# Common stuff
####################################

sub trim {
    my $s = shift;
    $s =~ s/^\s+//;
    $s =~ s/\s+$//;
    return $s;
}

sub timeStampToStr {
    my $ts = shift;
    return strftime("%a, %d %b %Y %H:%M:%S %z %Z", gmtime($ts));
}

sub printPrefix {
    my $timeStr = timeStampToStr(time());
    my $prefix  = shift;
    unshift(@_, ($timeStr . ' '));
    unshift(@_, $prefix);

    my $msg = join('', @_);
    chomp($msg);
    $msg = encode('UTF-8', $msg);
    local $| = 1;
    print(STDERR "$msg\n");
}

sub debug {
    printPrefix('[debug] ', @_) unless ($quiet2);
}

# level 2 debug
sub debug2 {
    printPrefix('[debug] ', @_);
}

sub debugTimes {
    my $msg = shift;
    my ($user, $system, $cuser, $csystem) = times();
    $msg = (defined($msg) ? ("($msg)") : '');
    debug("times $msg: $user/$system/$cuser/$csystem");
}

sub warning {
    printPrefix('[warn]  ', @_);
}

sub error {
    printPrefix('[error] ', @_);
}

sub fatal {
    error(@_);
    die(@_);
}

sub info {
    printPrefix('[info]  ', @_);
}

sub normalizeSpace {
    my $line = shift;
    $line =~ s/[\s]+/ /gso;
    $line =~ s/^[\s]*//gso;
    $line =~ s/[\s]$//gso;
    return $line;
}

####################################
# Global variables (continued)
####################################

my $msgEquivDef = undef;
my $userExpr    = undef;
my $userExprRe  = undef;
my $wantCaseI   = 0;
my $wantDup     = 0;
my $inverse     = 0;
my $wantDel     = 0;
my $userTempDir = undef;
my $quiet       = 0;
my $weakHash    = 0;

my %msgsMap     = ();
my $mcnt        = 0;
my $dupl        = 0;
my $matchCnt    = 0;

# mail parsing:
my %msg            = ();
my $msgStr         = '';        # raw
my $headerStr      = '';        # decoded
my $bodyStr        = '';        # decoded
my $msgHeaderStart = undef;     # raw

####################################
# Program routines
####################################

sub printHelp {
    my $ver           = VERSION();
    my $verdate       = VERSION_DATE();
    print STDERR <<"ENDHELP";
mboxgrep-perl.pl $ver ($verdate)

Copyright (C) 2011 Stanislaw Findeisen <stf at eisenbits.com>
License GPLv3+: GNU GPL version 3 or later <http://gnu.org/licenses/>
This is free software: you are free to change and redistribute it.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

Usage:
  $0 [OPTION]...

DESCRIPTION

mboxgrep-perl is a very simple mbox file parser. Features include:
* ability to grep on e-mail headers using regular expressions
* ability to filter out duplicate messages.

Each e-mail message encountered on input is processed once and classified
either as a match or not-match. Matching messages are printed out on
standard output. They can also be deleted from input files.

Using --dup you can filter out duplicate messages. There are 4 different ways
to define when 2 messages are equal.

OPTIONS

Input control

--source
    mbox file to parse. If this parameter is not specified, standard input
    is read. If this parameter is a directory, it is being read recursively.

E-mail matching

--equiv
    Message identity (equivalence relation) definition. Use 'message-id' for
    Message-ID header fields, 'identity' for binary identity (i.e. hashes
    over whole message) or 'content' for hashes over several fields (i.e.:
    Message-ID, Date, From, To, Cc, Subject, body prefix, body suffix).

    By default, all e-mail messages are considered different to each other.

    Note: not every e-mail message has Message-ID field. If this parameter
    is set to 'message-id' then all such messages will be considered identical
    (and a warning will be printed on standard error).

    Note: message equivalence has precedence over regular expression
    matching, i.e. if 2 messages are equivalent to each other and one of
    them matches the regex while the other does not, it is unspecified
    which one of them will be considered a match.

--expr
    Perl-compatible regular expression to match the e-mail header against.
    If this parameter is not specified, the expression is considered empty
    and is satisfied by every e-mail message.

    THIS IS A SECURITY HOLE (the expression is passed as-is to Perl's qr//).

-i
    The regular expression specified with --expr is case-insensitive.

--dup
    In order to match, the message must be a duplicate (in processing order),
    i.e. it must have been preceeded by some other, equivalent message
    (see --equiv).

-v
    Invert match, i.e. match messages that *do not* satisfy --expr *or are
    not* a duplicate (if --dup is specified).

Output control

--del
    Delete matching e-mail messages from input file(s).
    You'd better make a backup first!

--tmpDir
    Temporary directory to use.

-q
    Quiet mode: do not output any e-mails (just parse the file and report
    the count of matching e-mail messages).

--qq
    Be even more quiet: suppress debug messages. This implies -q.

Miscellaneous

--help
    Print this help message.

-w
    By default, mboxgrep-perl uses SHA-256 hashes. Use this option for MD5
    instead. This is weaker but may be faster.

BUGS

    This software was written on purpose and is not tested very well. Bug
    reports, comments, feature requests etc. are welcome:
    bug-report\@eisenbits.com .

ENDHELP
}

sub parseMsgEquivalenceDef {
    my $s = shift;

    if ($s =~ RE_MSGIDSTR_MID) {
        return C_MSGID_MID;
    } elsif ($s =~ RE_MSGIDSTR_IDENT) {
        return C_MSGID_IDENT;
    } elsif ($s =~ RE_MSGIDSTR_CONT) {
        return C_MSGID_CONT;
    } else {
        fatal("invalid message equivalence definition: $s");
    }
}

sub decodeHeaderField {
    my $s = shift;

    eval {
        $s = decode('MIME-Header', $s);
    };

    if ($@) {
        warning("MIME header decode: $@");
    }

    return $s;
}

sub getHash {
    my $s = shift;
    return (($weakHash) ? (md5($s)) : (sha256($s)));
}

sub getContentHash {
    my $hid    = $msg{HMSGID()};
    my $hdate  = $msg{HDATE()};
    my $hsubj  = $msg{HFROM()};
    my $hfrom  = $msg{HSUBJECT()};
    my $hto    = $msg{HTO()};
    my $hcc    = $msg{HCC()};

    my $bodyPref = substr($bodyStr, 0, 15);
    my $bodySufx = substr($bodyStr, -45);
    # debug("bodyPref: $bodyPref");
    # debug("bodySufx: $bodySufx");

    $hid   = '' unless defined($hid);
    $hdate = '' unless defined($hdate);
    $hsubj = '' unless defined($hsubj);
    $hfrom = '' unless defined($hfrom);
    $hto   = '' unless defined($hto);
    $hcc   = '' unless defined($hcc);

    my $hstr = encode_utf8("$hid $hdate $hsubj $hfrom $hto $hcc $bodyPref $bodySufx");
    return getHash($hstr);
}

sub getFullHash {
    return getHash($msgStr);
}

sub getMessageIdentity {
    if (C_MSGID_MID == $msgEquivDef) {
        if (defined($msg{HMSGID()})) {
            return ($msg{HMSGID()});
        } else {
            warning("Missing Message-ID field!\n\n$headerStr\n");
            return MESSAGE_ID_DEFAULT;
        }
    } elsif (C_MSGID_IDENT == $msgEquivDef) {
        return (getFullHash());
    } elsif (C_MSGID_CONT == $msgEquivDef) {
        return (getContentHash());
    } else {
        # we should never be here
        fatal("invalid msgEquivDef ($msgEquivDef)");
    }
}

sub outputMsg {
    my $fh = shift;
       $fh = \*STDOUT unless defined($fh);
    print ($fh $msgStr);
}

sub clearMessage {
    %msg       = ();
    $msgStr    = '';
    $headerStr = '';
    $bodyStr   = '';
}

# returns true iff successful parse
sub parseMessage {
    my $fh     = shift;
    my $inh    = 0;
    my $inb    = 0;
    my $line   = undef;

    if (defined($msgHeaderStart)) {
        $inh = 1;
        $msgStr    = $msgHeaderStart;
        $headerStr = decode_utf8($msgHeaderStart);
        undef($msgHeaderStart);
    }

    while ($line = <$fh>) {
        # Well, this decoding is probably wrong, especially if we are in the body.
        # But we just want it for a hash.
        my $lineStr = decode_utf8($line);

        if ($lineStr =~ RE_HEADER_START) {
            $msgHeaderStart = $line;

            if ($inh or $inb) {
                # already in the next message, exit
                return 1;
            } else {
                # message start
                $inh = 1;
                $msgStr    = $msgHeaderStart;
                $headerStr = decode_utf8($msgHeaderStart);
                undef($msgHeaderStart);
            }
        } else {
            if ($inh or $inb) {
                $msgStr .= $line;
            } else {
                # not a mbox file...
                return -1;
            }

            if ($inh) {
                if ($lineStr =~ RE_HEADER_FIELD) {
                    my $fieldNameLC = lc($1);
                    my $fieldValue  = $2;

                    if ('message-id' eq $fieldNameLC) {
                        $msg{HMSGID()} .= decodeHeaderField($fieldValue);
                    } elsif ('from' eq $fieldNameLC) {
                        $msg{HFROM()} .= decodeHeaderField($fieldValue);
                    } elsif ('to' eq $fieldNameLC) {
                        $msg{HTO()} .= decodeHeaderField($fieldValue);
                    } elsif ('cc' eq $fieldNameLC) {
                        $msg{HCC()} .= decodeHeaderField($fieldValue);
                    } elsif ('date' eq $fieldNameLC) {
                        $msg{HDATE()} .= decodeHeaderField($fieldValue);
                    } elsif ('subject' eq $fieldNameLC) {
                        $msg{HSUBJECT()} .= decodeHeaderField($fieldValue);
                    }
                }

                if ($line =~ RE_BODY_START) {
                    $inh = 0;
                    $inb = 1;
                } else {
                    $headerStr .= $lineStr;
                }
            } elsif ($inb) {
                $bodyStr .= $lineStr;
            }
        }
    }

    return (($inh or $inb) ? 1 : 0);
}

sub checkMsgMatch {
    # debug('Message-ID: ' . $msg{HMSGID()})   if (defined($msg{HMSGID()}));
    # debug('Date:       ' . $msg{HDATE()})    if (defined($msg{HDATE()}));
    # debug('From:       ' . $msg{HFROM()})    if (defined($msg{HFROM()}));
    # debug('Subject:    ' . $msg{HSUBJECT()}) if (defined($msg{HSUBJECT()}));
    # debug('To:         ' . $msg{HTO()})      if (defined($msg{HTO()}));
    # debug('Cc:         ' . $msg{HCC()})      if (defined($msg{HCC()}));

    if (C_MSGID_NONE == $msgEquivDef) {
        return ($inverse ? 1 : 0) if ($wantDup);
    } else {
        my $msgIdentity = getMessageIdentity();

        if ($msgsMap{$msgIdentity}) {
            # a duplicate
            $msgsMap{$msgIdentity} += 1;
            $dupl++;
            debug('Duplicate message: ' . (($msg{HMSGID()}) or '<unknown>') . ' (' . ($msgsMap{$msgIdentity}) . ')');
        } else {
            $msgsMap{$msgIdentity} = 1;
            return ($inverse ? 1 : 0) if ($wantDup);
        }
    }

    if (defined($userExprRe)) {
        # TODO this is a security hole
        if ($headerStr =~ $userExprRe) {
            return ($inverse ? 0 : 1);
        } else {
            return ($inverse ? 1 : 0);
        }
    } else {
        return ($inverse ? 0 : 1);
    }
}

# a single mbox file parsing
sub parseFile {
    my $fname    = shift;
    my $fh       = undef;
    my $fhTmp    = undef;
    my $tmpName  = undef;
    my $fileMsgs = 0;
    my $notMbox  = 0;

    if (defined($fname)) {
        open($fh, '<', $fname) or fatal("Cannot open file ($fname): " . ($!));

        if ($wantDel) {
            my %tmpParams = (UNLINK => 0);
               $tmpParams{DIR} = $userTempDir if (defined($userTempDir));
            ($fhTmp, $tmpName) = tempfile(%tmpParams);
            info("deleting messages from $fname ; tmp is: $tmpName");
        } else {
            info("Parsing: $fname");
        }
    } else {
        info('Parsing STDIN...');
        $fh = \*STDIN;
    }

    while (1) {
        my $p = parseMessage($fh);

        if (1 == $p) {
            $fileMsgs++;
            $mcnt++;

            my $mm = checkMsgMatch();

            if ($mm) {
                $matchCnt++;
                outputMsg() unless ($quiet);
            } elsif ($wantDel) {
                outputMsg($fhTmp);
            }

            clearMessage();
        } else {
            if (-1 == $p) {
                $notMbox = 1;
                warning('Not a mbox file...' . ((defined($fname)) ? (" ($fname)") : ''));
            }
            last;
        }
    }

    if (defined($fname)) {
        close($fh);

        if ($wantDel) {
            close($fhTmp);

            if ($fileMsgs and (not $notMbox)) {
                debug("$tmpName => $fname");
                move($tmpName, $fname) or fatal("Could not move $tmpName => $fname: $!");
            } else {
                unlink($tmpName) or warning("Could not unlink $tmpName: $!");
            }
        }
    }
}

# recursively scans a directory
sub parseDir {
    my $dirName = shift;

    if (opendir(my $dh, $dirName)) {
        my @dirItems = sort readdir($dh);
        my @dirFiles = grep {-f "$dirName/$_"} @dirItems;

        foreach my $item (@dirItems) {
            next if ('.' eq $item) or ('..' eq $item);
            my $itemFull = "$dirName/$item";

            if (-d $itemFull) {
                parseDir($itemFull);
            } elsif (-f $itemFull) {
                # regular file
                parseFile($itemFull);
            }
        }

        closedir($dh);
    } else {
        warning("Can't read dir: $dirName");
    }
}

####################################
# The program - main
####################################

my $help          = 0;
my $msgEquivStr   = undef;
my $InputFileName = undef;
my $clres = GetOptions('source=s' => \$InputFileName, 'equiv=s' => \$msgEquivStr, 'expr=s' => \$userExpr, 'i' => \$wantCaseI, 'dup' => \$wantDup, 'v' => \$inverse, 'del' => \$wantDel, 'tmpDir=s' => \$userTempDir, 'q' => \$quiet, 'qq' => \$quiet2, 'help'  => \$help, 'w' => \$weakHash);

if ($help) {
    printHelp();
    exit 0;
}

if (defined($userExpr)) {
    # TODO this is a security hole
    $userExprRe = ($wantCaseI ? (qr/$userExpr/moi) : (qr/$userExpr/mo));
    debug("user regex = $userExprRe");
}

debug("wantDup")  if ($wantDup);
debug("invert match")  if ($inverse);
debug("wantDel")  if ($wantDel);
debug("userTempDir = $userTempDir")  if (defined($userTempDir));

$quiet = 1 if ($quiet2);
$msgEquivDef = C_MSGID_NONE;
$msgEquivDef = parseMsgEquivalenceDef($msgEquivStr) if ($msgEquivStr);
debug('using ' . (($weakHash) ? 'MD5' : 'SHA-256') . ' hash');

if ((defined($InputFileName)) and (-d $InputFileName)) {
    parseDir($InputFileName);
} else {
    fatal('You must specify a source file to use --del.') if ($wantDel and (not (defined($InputFileName))));
    # this may or may not be a regular file - we don't care
    parseFile($InputFileName);
}

info("Found $mcnt messages ($dupl duplicates). Matches: $matchCnt.");
