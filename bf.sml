(* bf.sml: a brainfuck interpreter in Standard ML *)

(* {{{ Quicksort *)

fun filter pred [] = []
  | filter pred (x::xs) =
  if pred x 
  then (x :: (filter pred xs)) 
  else filter pred xs

fun qsort_k _ _ [] = []
  | qsort_k _ _ [x] = [x]
  | qsort_k asc kfn (x::xs) =
  let val lt = filter (fn y => ((kfn y) <= (kfn x))) xs
      val gt = filter (fn y => ((kfn y) > (kfn x))) xs
      val lhs = (qsort_k asc kfn lt)
      val rhs = (qsort_k asc kfn gt)
  in
    if asc 
    then lhs @ (x::rhs)
    else rhs @ (x::lhs)
  end

(* Ascending and descending sorts. *)
fun asort_k kfn = qsort_k true kfn;
fun dsort_k kfn = qsort_k false kfn;

fun asort xs = asort_k (fn x => x) xs;
fun dsort xs = dsort_k (fn x => x) xs;

(* }}} *)
(* {{{ Functional array implementation *)

datatype 'a FNA =
    ANode of ('a FNA) * ('a option) * ('a FNA)
  | ALeaf;

exception Index;

fun fna_find ALeaf _ = NONE
  | fna_find (ANode(l,v,r)) k =
  if k < 0 then raise Index
  else if k = 0 then v
  else if (k mod 2) = 0 then
    fna_find l ((k div 2) - 1)
  else
    fna_find r ((k-1) div 2);

fun fna_update ALeaf k v' =
    if k < 0 then raise Index
    else if k = 0 then ANode(ALeaf, SOME(v'), ALeaf)
    else if (k mod 2) = 0 then
      let val stree = fna_update ALeaf ((k div 2) - 1) v'
      in ANode(stree, NONE, ALeaf)
      end
    else
      let val stree = fna_update ALeaf ((k-1) div 2) v'
      in ANode(ALeaf, NONE, stree)
      end
  | fna_update (ANode(l,v,r)) k v' =
    if k < 0 then raise Index
    else if k = 0 then ANode(l, SOME(v'), r)
    else if (k mod 2) = 0 then
      let val stree = fna_update l ((k div 2) - 1) v'
      in ANode(stree, v, r)
      end
    else
      let val stree = fna_update r ((k-1) div 2) v'
      in ANode(l, v, stree)
      end;

local
fun l2fna_iter [] _ = ALeaf
  | l2fna_iter (x::xs) i =
    fna_update (l2fna_iter xs (i+1)) i x
in
  fun list_to_fna lst = l2fna_iter lst 0
end

fun fna_kvlist fna = 
let
  fun fna2list_iter ALeaf f = []
    | fna2list_iter (ANode(l,v,r)) f =
      let 
        val left  = fna2list_iter l (fn x => f (2*x + 2))
        val right = fna2list_iter r (fn x => f (2*x + 1))
      in
        case v of
             NONE => left @ right
           | (SOME(a)) => left @ ((f 0, a)::right)
      end
in fna2list_iter fna (fn x => x)
end

fun fna_to_list placeholder fna =
let
  val kvlist = asort_k (fn (k,v) => k) (fna_kvlist fna)
  fun iter _ [] = []
    | iter n ((k,v)::kvs) =
    if k=n then v :: (iter (n+1) kvs)
    else placeholder :: (iter (n+1) ((k,v)::kvs))
in
  iter 0 kvlist
end

fun fna_to_string stringer fna =
let
fun fna2string ALeaf = "."
  | fna2string (ANode(l,v,r)) =
  case v of
    NONE => "-"
  | (SOME(a)) => (stringer a ^ " -> (" ^ (fna2string l) ^ ", " ^ (fna2string r) ^ ")")
in fna2string fna
end

(* }}} *)
(* {{{ Representations, parsing, and transformations *)

(* Raw instruction set *)
datatype Inst = 
  Inc | Dec | Right | Left | 
  LoopStart | LoopEnd | Read | Write;

(* "First transformation" instruction set *)
datatype AlphaInst =
  AInc | ADec | ARight | ALeft 
       | ALoopTo of int | ALoopFrom of int
       | ARead | AWrite;

exception Parse of string;
exception Stuck of string;

fun inst_str Inc = "+"
  | inst_str Dec = "-"
  | inst_str Right = ">"
  | inst_str Left = "<"
  | inst_str LoopStart = "["
  | inst_str LoopEnd = "]"
  | inst_str Write = "."
  | inst_str Read = ",";

fun char_to_inst #"+" =  SOME(Inc)
  | char_to_inst #"-" =  SOME(Dec)
  | char_to_inst #">" =  SOME(Right)
  | char_to_inst #"<" =  SOME(Left)
  | char_to_inst #"[" =  SOME(LoopStart)
  | char_to_inst #"]" =  SOME(LoopEnd)
  | char_to_inst #"." =  SOME(Write)
  | char_to_inst #"," =  SOME(Read)
  | char_to_inst _ = NONE;

fun only_some [] = []
  | only_some (NONE :: xs) = only_some xs
  | only_some (SOME(a) :: xs) = a :: (only_some xs)

fun bf_lex code =
  only_some (map char_to_inst (explode code));

(* Helper functions for the transformation *)
local
fun bfa_trivial Inc = AInc
  | bfa_trivial Dec = ADec
  | bfa_trivial Right = ARight
  | bfa_trivial Left = ALeft
  | bfa_trivial Read = ARead
  | bfa_trivial Write = AWrite
  | bfa_trivial LoopStart = ALoopTo(0)
  | bfa_trivial LoopEnd = ALoopFrom(0)

fun bfa_pairs [] _ _ = []
  | bfa_pairs ((LoopStart)::insts) i js = bfa_pairs insts (i+1) (i::js)
  | bfa_pairs ((LoopEnd)::insts) i (j::js) = (j,i) :: (bfa_pairs insts (i+1) js)
  | bfa_pairs ((LoopEnd)::insts) _ _ = raise (Parse "mismatched loop")
  | bfa_pairs (inst::insts) i js = bfa_pairs insts (i+1) js

fun transform_fna fna [] = fna
  | transform_fna fna ((i,j)::ijs) =
    transform_fna (fna_update (fna_update fna j (ALoopFrom(i+1))) i
    (ALoopTo(j+1))) ijs;

in
  fun bf_alpha lst =
  let val fna = list_to_fna (map bfa_trivial lst)
      val pairs = bfa_pairs lst 0 []
  in transform_fna fna pairs
  end
end

fun bf_parse code = bf_alpha (bf_lex code)

(* }}} *)
(* {{{ Core Implementation *)

type BFTape = AlphaInst FNA;
type BFStore = Word8.word FNA;

fun bf_fetch store hp =
  case (fna_find store hp) of
    NONE => 0
  | (SOME(b)) => Word8.toInt b

fun bf_store store hp v =
  fna_update store hp (Word8.fromInt v);

fun bf_run tape = 
let fun step (store, pc, hp) =
  case (fna_find tape pc) of
    NONE => NONE
  | (SOME(inst)) => (
  let val config' =
  (case inst of
    AInc =>
      let 
      val v = bf_fetch store hp
      val store' = bf_store store hp (v+1)
      in (store', pc+1, hp) end
  | ADec =>
      let 
      val v = bf_fetch store hp
      val store' = bf_store store hp (v-1)
      in (store', pc+1, hp) end
  | ARight => (store, pc+1, hp+1) 
  | ALeft =>
      if hp = 0 then raise (Stuck "Left end of store.")
      else (store, pc+1, hp-1)
  | ALoopTo(to) =>
      if (bf_fetch store hp)=0
      then (store, to, hp)
      else (store, pc+1, hp)
  | ALoopFrom(from) =>
      if (bf_fetch store hp)=0
      then (store, pc+1, hp)
      else (store, from, hp)
  | ARead => raise (Stuck "Not yet implemented.")
  | AWrite => 
      let val v = bf_fetch store hp
      in
      print (String.str (Byte.byteToChar (Word8.fromInt v)));
      (store, pc+1, hp)
      end
      )
  in
    SOME(config')
  end)
  fun bf_iter config = 
    case step config of
      NONE => ()
    | (SOME(c')) => bf_iter c'
in
  bf_iter (ALeaf, 0, 0)
end;

fun interpret code = bf_run (bf_parse code);

fun bf_load fname =
  let
    val ins = TextIO.openIn fname
    fun riter ins =
      case TextIO.inputLine ins of
        SOME line => (line ^ (riter ins))
      | NONE => ""
    val code = (riter ins)
  in
    print code; interpret code; TextIO.closeIn ins
  end;

(* }}} *)

fun main () = 
  case CommandLine.arguments() of 
       [] => ()
     | (x::xs) => bf_load x

(* 
 * vim: foldmethod=marker 
 *)
