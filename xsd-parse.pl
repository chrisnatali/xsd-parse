#!/usr/bin/perl

#-----------------------------------------------------------
# Builds a graph of dependencies between global xsd
# entities.   
#
#----------------------------------------------------------- 
# Input
# List of xsd files (defined in terms of w3.org xsd spec)
#
#----------------------------------------------------------- 
# Output (2 files)
#
#  There is a common format for an xsd entity across 
#  files.  It is based on what is required to uniquely 
#  identify a global xsd entity.  This is referenced by 
#  below format definitions.
#
#  xsd_entity:  {<namespace>}<entity_name>,<xsd_type>
#      example:  {http://www.xyz.com/v1}Org,element 
#
#  entities:  
#    List of unique xsd entities (1 per line)
#    format:  <xsd_entity> <filename>
#      example:  {http://www.xyz.com/v1}Org,element Org.xsd
#
#  refs:
#    Flattened dependence graph between global xsd entities
#    1 parent-child relation per line 
#    format:  <xsd_entity> <xsd_entity> <depth>
#      example:  {xyz}Org,element {xyz}OrgType,complexType 1
#        This represent an Org element with a direct 
#        (hence depth=1) dependence on the OrgType
#        complexType
#
#  Any errors/warnings are written to STDERR

use File::Basename;
use Cwd;

# pre-declaring parameter-less functions
# (so we don't need paren's when calling)
sub elements;
sub element;

#-----------------------------------------------------------
# Globals

my $g_sequence = 0; # for adding a uniq id to nodes
my @g_ns; # temp stack used for namespace lookup
my @g_file_stack;  # temp stack rep'ing include file hierarchy
my %g_processed_files; # hash of input (and included) files
my @g_entity_output; # entity output strings
my @g_ref_output; # ref output strings
my @errors;  # list of error strings (sent to stderr)

# g_node is a hash that maintains the xsd entities
# g_nodes = { 
#  type => (xsd types, i.e. complexType) {
#   name => (unique (for type) qname of xsd entity) {
#    name => string (qname, match hash key above),
#    file => string (filename where xsd entity defined),
#    xsd_type => string (the xsd type, match outer type),
#    ref|base|type => string (ref to another qname),
#    elts => [ref to recursive hash] (list of sub entities),
#    refs => [ 
#      { 
#        depth => number ( depth of ref in xsd tree )
#        ref   => ref to recursive hash
#      }
#    ]
#   }
#  }
# }
my $g_nodes = {};

# temp stack rep'ing xsd hierarchy
# used for looking up parent names
my @t_nodes;  

# temp stack rep'ing xsd reference hierarchy
# used when building refs to find cycles and depth
my @g_ref_stack; 

#----------------------------------------------------------- 

#-----------------------------------------------------------
# XSD Specific "Constants"

my $XS_NS           = "http://www.w3.org/2001/XMLSchema";
my $XS_SCHEMA       = "{$XS_NS}schema";
my $XS_ELEMENT      = "{$XS_NS}element";
my $XS_COMPLEX_TYPE = "{$XS_NS}complexType";
my $XS_SIMPLE_TYPE  = "{$XS_NS}simpleType";
my $XS_EXTENSION    = "{$XS_NS}extension";
my $XS_INCLUDE      = "{$XS_NS}include";
my $XS_IMPORT       = "{$XS_NS}import";
my $XS_GROUP        = "{$XS_NS}group";
my $XS_ATTRIBUTE    = "{$XS_NS}attribute";
my $XS_RESTRICTION  = "{$XS_NS}restriction";
my @XS_TYPES        = (   
                         $XS_SCHEMA, 
                         $XS_ELEMENT,
                         $XS_COMPLEX_TYPE,
                         $XS_SIMPLE_TYPE,
                         $XS_EXTENSION,
                         $XS_INCLUDE,
                         $XS_IMPORT,
                         $XS_RESTRICTION,
                         $XS_GROUP,
                         $XS_ATTRIBUTE,
                       );

my $SCHEMA       = "schema";
my $ELEMENT      = "element";
my $COMPLEX_TYPE = "complexType";
my $SIMPLE_TYPE  = "simpleType";
my $EXTENSION    = "extension";
my $INCLUDE      = "include";
my $IMPORT       = "import";
my $GROUP        = "group";
my $ATTRIBUTE    = "attribute";
my $RESTRICTION  = "restriction";

# xsd simple types
my @SIMPLE_TYPES = ("integer", 
                    "int", 
                    "byte", 
                    "short", 
                    "duration", 
                    "long", 
                    "string", 
                    "normalizedString", 
                    "decimal",
                    "float",
                    "double",
                    "boolean",
                    "base64Binary",
                    "date",
                    "token",
                    "positiveInteger",
                    "anyType",
                    "ID",
                    "QName",
                    "NCName",
                    "dateTime",
                    "anyURI",
                    "gYear",
                    "gYearMonth",
                    "hexBinary",
                    "language",
                    "negativeInteger",
                    "nonNegativeInteger",
                    "nonPositiveInteger",
                    "time");
                         
# prepopulate xsd simple types
for (@SIMPLE_TYPES) {
  my $name = "{$XS_NS}$_";
  $g_nodes->{$SIMPLE_TYPE}->{$name} = {
    name => $name, 
    xsd_type => $SIMPLE_TYPE
  }; 
}
#-----------------------------------------------------------

#-----------------------------------------------------------
# Visitor function refs
my $index_nodes = sub {
  my $node = $_[0];
  $node->{id} = $g_sequence++;
};

my $proc_refs = sub {
  my $node = $_[0];
  push @g_ref_stack, $node;
  my @refs = print_refs($node);
  @{$node->{refs}} = @refs;
  my $ct_err = @errors;
  my $ct_ref = @refs;
  my $ct_stack = @g_ref_stack;
  pop @g_ref_stack;
};

my $set_entity_output= sub {
  my $entity = $_[0];
  my $id = $entity->{id};
  my $name = $entity->{name};
  my $xsd_type = $entity->{xsd_type};
  my $file = $entity->{file};
  print ENTITY_OUT "$name,$xsd_type $file\n";
  # push @g_entity_output, "$name,$xsd_type $file";
  # for my $ref ( @{$entity->{refs}} ) {
  #  my $r_name = $ref->{ref}->{name};
  #  my $r_type = $ref->{ref}->{xsd_type};
  #  my $depth = $ref->{depth};
  #  print REF_OUT "$name,$xsd_type $r_name,$r_type $depth\n";
  #  push @g_ref_output, "$name,$xsd_type $r_name,$r_type $depth";
  #}
};
#-----------------------------------------------------------

#-----------------------------------------------------------
# Start Processing

# process each input xsd
my $g_top_work_dir = `pwd`;
while(chop($file = <STDIN>)) {
  proc_file($file);
  `cd $g_top_work_dir`;
}

# At this point g_nodes is populated with all "global"
# xsd entities (but dependencies are not fully analyzed)
visit($index_nodes); # Add identifier
# print "complexTypes: " . scalar(keys(%{$g_nodes->{"complexType"}})) . "\n";
# print "elements: " . scalar(keys(%{$g_nodes->{"element"}})) . "\n";

open(REF_OUT, ">refs") || die "Failed to write refs";
visit($proc_refs);  # Analyze and PRINT dependencies 
close(REF_OUT);

# print entities 
open(ENTITY_OUT, ">entities") || die "Failed to write entities";
visit($set_entity_output); # Print global entities
close(ENTITY_OUT);

# for my $err (@errors) {
#   warn "$err\n";
# }

#-----------------------------------------------------------

#-----------------------------------------------------------
# Functions

# Visit all nodes, calling passed in function on them
sub visit {
  my $coderef = $_[0];
  for my $type (keys %{$g_nodes}) {
    my $type_hash = $g_nodes->{$type};
    for my $name (keys %{$type_hash}) {
     my $entity = $type_hash->{$name};
     $coderef->($entity);
    }
  }
}

# Lookup the global xsd entity by type, attribute and qname
sub lookup_ref {
  my $type = $_[0];
  my $attr = $_[1];
  my $ref_name = $_[2];
  if ( $type eq $ELEMENT and $attr eq "ref" ) {
    return $g_nodes->{$ELEMENT}->{$ref_name};
  }
  if ( $type eq $ELEMENT and $attr eq "type" ) {
    return ( $g_nodes->{$SIMPLE_TYPE}->{$ref_name} ||
             $g_nodes->{$COMPLEX_TYPE}->{$ref_name} );
  }
  if ( $type eq $ATTRIBUTE and $attr eq "ref" ) { 
    return $g_nodes->{$ATTRIBUTE}->{$ref_name};
  }
  if ( $type eq $ATTRIBUTE and $attr eq "type" ) { 
    return $g_nodes->{$SIMPLE_TYPE}->{$ref_name};
  }
  if ( $type eq $EXTENSION and $attr eq "base" ) {
    return ( $g_nodes->{$SIMPLE_TYPE}->{$ref_name} ||
             $g_nodes->{$COMPLEX_TYPE}->{$ref_name} );
  }
  if ( $type eq $RESTRICTION and $attr eq "base" ) {
    return ( $g_nodes->{$SIMPLE_TYPE}->{$ref_name} ||
             $g_nodes->{$COMPLEX_TYPE}->{$ref_name} );
  }
  if ( $type eq $GROUP and $attr eq "ref" ) { 
    return $g_nodes->{$GROUP}->{$ref_name};
  }
}

# Print ALL global xsd entities that this node depends on
# The time complexity is O(N^N) because for each node, there
# is the potential to visit every other node at n-1 
# recursive levels.
# Disk space is also exponential in the # of nodes.
# Dynamic memory space complexity is O(N) since we don't 
# maintain the graph in RAM (it's printed as we go)
sub print_refs {
  my $node = $_[0];
  my $type = $node->{xsd_type};
  my $name = $node->{name};
  for my $elt (@{$node->{elts}}) {
    print_refs($elt);
  }
  for my $attr ( grep {/^ref$|^base$|^type/} keys %{$node} ) { 
    my $p_node = $g_ref_stack[0];
    my $ref_name = $node->{$attr};
    my $ref = lookup_ref($type, $attr, $ref_name);
    if ( !$ref ) {
      warn "Bad $type reference to $ref_name from $name via $attr\n";
      last;
    }
    
    my $depth = scalar(@g_ref_stack);
    my $p_name = $p_node->{name};
    my $p_type = $p_node->{xsd_type};
    my $r_name = $ref->{name};
    my $r_type = $ref->{xsd_type};
    print REF_OUT "$p_name,$p_type $r_name,$r_type $depth\n";
    # do NOT recurse if we find a cycle
    if ( grep(($ref == $_), @g_ref_stack) ) {
      warn "$type reference Cycle found from $name to $ref_name";
      last;
    }
    push @g_ref_stack, $ref;
    print_refs($ref);
    pop @g_ref_stack;
  }
}

# Get ALL global xsd entities that this node depends on
sub get_refs {
  my $node = $_[0];
  my $type = $node->{xsd_type};
  my $name = $node->{name};
  my @refs;
  for my $elt (@{$node->{elts}}) {
    my @elt_refs = get_refs($elt);
    if ( @elt_refs > 0) {
      push @refs, @elt_refs; 
    }
  }
  for my $attr ( grep {/^ref$|^base$|^type/} keys %{$node} ) { 
    my $ref_name = $node->{$attr};
    my $ref = lookup_ref($type, $attr, $ref_name);
    if ( !$ref ) {
      warn "Bad $type reference to $ref_name from $name via $attr\n";
      last;
    }
    push @refs, { depth => scalar(@g_ref_stack), 
                  ref   => $ref };
    # do NOT recurse if we find a cycle
    if ( grep(($ref == $_), @g_ref_stack) ) {
      warn "$type reference Cycle found from $name to $ref_name\n";
      last;
    }
    push @g_ref_stack, $ref;
    push @refs, get_refs($ref);
    pop @g_ref_stack;
  }
  return @refs;
}
    
# Process XSD file 
# Recursive (via parse) 
# Side Effect:  g_node has global xsd entities
sub proc_file {
  my $rel_file = $_[0];
  $rel_file =~ s/\\/\//g;
  my $rel_dir = dirname($rel_file);
  my $base_file = basename($rel_file);
  my $abs_dir = `cd $rel_dir; pwd`;
  $abs_dir =~ s/\n//;
  my $xsd_file = "$abs_dir/$base_file";
  if ( !$g_processed_files{$xsd_file} ) {
    $g_processed_files{$xsd_file} = { status => "started" };
    push @g_file_stack, $xsd_file;
    parse($xsd_file);
    for my $include (@{$g_processed_files{$xsd_file}->{includes}}) {
      proc_file("$abs_dir/$include");
    }
    $g_processed_files{$xsd_file}->{status} = "complete";
    pop @g_file_stack;
  }
  `cd $abs_dir`;

}
  
sub parse_ns {
  my $elt = $_[0];
  my $ns;
  if ($elt->{attrs}) {
    for (keys %{$elt->{attrs}}) {
      # careful to handle the empty prefix case
      if ( /^xmlns(:(\w*))?/ ) {
        $ns->{$2} = $elt->{attrs}->{$_};
      }
      if ( /targetNamespace/ ) {
        $ns->{targetNamespace} = $elt->{attrs}->{$_};
      }
    }
  }
  return $ns;
}

# look through stack of ns maps to retrieve full namespace
sub get_ns {
  my $prefix = $_[0];
  for (reverse @g_ns) { 
    if ( $_->{$prefix} ) { return $_->{$prefix}; }
  }
}

# get our internal name/qname format for the 
# optionally prefixed element name
sub get_name_qname {
  my $_ = $_[0];
  my $prefix = "";
  my $name = $_;
  if ( /(\w*):(\w*)/ ) {
    $prefix = $1;
    $name = $2;
  }
  my $ns = get_ns($prefix);
  if ( $ns ) {
    return ($name, "{$ns}$name");
  } else { 
    return $name;
  }
   
}

sub get_parent_global_qname {
  for my $n (reverse @t_nodes) {
    if ( $n->{name} ) { return $n->{name}; }
  }
}

# global qname includes parent name if element is "local"
sub get_global_qname {
  my $name = $_[0]->{attrs}->{name};
  if ( !$name ) { return ""; }
  my $parent_qname = get_parent_global_qname;
  if ( $parent_qname ) {
    return "$parent_qname/$name";
  } else {
    # must be top-level
    my $target_ns = $g_ns[$#g_ns]->{targetNamespace};
    return "{$target_ns}$name";
  }
}

# get the ref qname and the attribute key that ref'd it
sub get_ref_type {
  my $node = $_[0];
  for my $a (grep {/^ref$|^base$|^type$/} keys %{$node->{attrs}}) {
    my ($name, $ref) = get_name_qname($node->{attrs}->{$a});
    return ($ref, $a);
  }
}  
      
# Recursively process raw xml elements as xsd elements
sub proc_node {
  my $node = $_[0]; 
  my $parent_file = $g_file_stack[$#g_file_stack];

  # handle namespaces
  my $ns = parse_ns($node);
  if ( $ns ) { push @g_ns, $ns; } 

  my ($type, $node_name) = get_name_qname($node->{name});
  
  # push included files onto stack for processing
  if ($type eq $INCLUDE || $type eq $IMPORT) {
    my $include_file = $node->{attrs}->{"schemaLocation"};
    push @{$g_processed_files{$parent_file}->{includes}}, $include_file;
  }
  
  # if this is a type we're interested in
  # create a global node and push it onto the stack
  my $xs_node;
  if ( grep(/^$node_name$/, @XS_TYPES) ) {
    $xs_node->{file} = $parent_file;
    $xs_node->{xsd_type} = $type; 
    my $name = get_global_qname($node);
    $xs_node->{name} = $name;
    my ($ref, $ref_type) = get_ref_type($node);
    if ($ref_type) { $xs_node->{$ref_type} = $ref; }

    # add to global node hash IF it's top level
    if ( scalar(@t_nodes) and $t_nodes[$#t_nodes]->{xsd_type} eq $SCHEMA ) {
      if ( $g_nodes->{$type}->{$name} ) {
        warn "Overwriting global $type named $name\n";
      }
      $g_nodes->{$type}->{$name} = $xs_node;
    }
    
    # append this "child" to parent if there is one
    if ( scalar(@t_nodes) ) {
      push @{$t_nodes[$#t_nodes]->{elts}}, $xs_node;
    }
    push @t_nodes, $xs_node;
  }
 
  # process all children
  for (@{$node->{elts}}) {
    proc_node($_);
  }
  if ( $xs_node ) { pop @t_nodes; }
  if ( $ns ) { pop @g_ns; }
}
   
sub parse {

  # slurp the file into $_
  my $f = $_[0]; 
  my $tmp_rs = $/;
  my $elts;
  undef $/;
  my $fh;
  open($fh, "< $f");
  $_ = <$fh>;
  close($fh);
  $/ = $tmp_rs;  # reset perl record delim

  # parse the xml elements 
  s/^\s*//;
  if ( s/^<\?xml[^\?]*\?>// ) { 
    $elts = elements;  
  }
    
  # process the xml elements into xsd tree
  my @top_elts = grep(($_->{xml_type} eq 'element'), @{$elts});
  for (@top_elts) {
    proc_node($_);
  }
}
  
sub elements {
  s/^\s*//;
  my $elts = [];

  # while we haven't reached the end of file
  # OR the end of a "parent" element
  while( !/^$/ && !/^<\// ) {
    # handle comments
    if ( /^<!--/ ) {
      if ( s/^<!--\s*((?:(.|\s))*?)-->// ) {
        push @{$elts}, {
                         xml_type => "comment",
                         value => $1
                       };
      } else { 
        warn format_error("invalid comment. ") . "\n";
        last 
      };
    }
    # text
    elsif ( /^[^<]/ ) { 
      if ( s/^([^<]*)// ) {
        push @{$elts}, { 
                        xml_type => "text", 
                        value => $1
                      };
      } else {
        warn format_error("invalid text element. ") . "\n";
        last;
      }
    }   
    # elements
    elsif ( /^<[A-Za-z]/ ) {
      my $elt = element;
      if ( !$elt )  { last };
      push @{$elts}, $elt;
    }
    # error
    else {
      warn format_error("error ") . "\n";
      last; 
    }
    s/^\s*//;
  }
  return $elts;
}

sub element {

  # get the element name
  if ( !s/^<([^\s>\/]*)\s*// ) {
    warn format_error("error ") . "\n";
    return false;
  }
  my $elt_name = $1;
  my $attrs = {};
  
  # get the attributes
  while( s/^([\w:]+)\s*=\s*(["'])((?:(?!\2).)*)\2\s*// ) {
    $attrs->{$1} = $3;
  }

  # check if the element is closed
  if( s/^\/>// ) {
    return { name  => $elt_name, 
             xml_type  => 'element',
             attrs => $attrs };
  } else {
    if ( s/^>// ) {
      my $elts = elements;
      
      # match the start element
      if ( s/^<\/\Q$elt_name\E>// ) {
        return { name  => $elt_name,
                 xml_type  => 'element',
                 attrs => $attrs,
                 elts  => $elts };
      } else { 
        warn format_error("complex element $elt_name not ended correctly.") . "\n";
        return false; 
      } 
    } else {
      warn format_error("simple element $elt_name not ended correctly.") . "\n";
    }
  }    
}

sub format_error {
  my $err_str = $_[0];
  $err_str = $err_str . " near (" . substr($_, 0, 20) . ") in $g_file_stack[$#g_file_stack]";
  return $err_str;
}
