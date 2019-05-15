(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

(** This file contains a library for encoding binary trees into
    lists of Boolean values in {Zero,One} 
    
    The proofs contain holes that have to be filled by students
*)

Require Import List Arith Omega Wellfounded.

Set Implicit Arguments.

(** To reason or compute by induction on a measure *)

Theorem measure_rect X (m : X -> nat) (P : X -> Type) :
      (forall x, (forall y, m y < m x -> P y) -> P x) -> forall x, P x.
Proof. apply well_founded_induction_type, wf_inverse_image, lt_wf. Qed.

(** To reason by induction on the length of lists *)

Definition list_length_rect X := measure_rect (@length X).

(* And a friendly notation for this induction principle on lists *)

Tactic Notation "induction" "on" "length" "of" ident(x) "as" simple_intropattern(H) := 
  induction x as H using list_length_rect.
  
(* A small library with a tactic to rewrite length *)

Section length.
   
  Variables (X : Type) (x : X) (l : list X).

  Fact length_nil  : length (@nil X) = 0.             Proof. auto. Qed.
  Fact length_cons : length (x::l)   = S (length l).  Proof. auto. Qed.

End length.

Create HintDb length_db.

Tactic Notation "rew" "length" := autorewrite with length_db.
Tactic Notation "rew" "length" "in" hyp(H) := autorewrite with length_db in H.
Hint Rewrite length_nil length_cons app_length map_length : length_db.

(** A small complement for the list library *)

(* If a list is cut in half in two different way l1 ++ r1 = l2 ++ r2
   and the cut is at the same place then l1 = l2 and r1 = r2 *)

Fact list_app_inj X (l1 l2 r1 r2 : list X) : length l1 = length l2 -> l1++r1 = l2++r2 -> l1 = l2 /\ r1 = r2.
Proof.
  revert l2; induction l1 as [ | x l1 IH ]; intros [ | y l2 ].
  +intros H1 H2.
  split;trivial.
  (*auto. fonctionne pour remplacer split;trivial.*)
  +intros H1 H2.
  inversion H1. (*hypothèse fausse*)
  +intros H1 H2.
  inversion H1.
  +intros H1 H2.
  injection H2.
  intros H3 H4.
  subst. (* y:X et x:X -> x:y *) 
  case (IH l2);auto. 
  intros H4 H5.
  subst.
  split;trivial.
Qed.

Section flat_map.

  Variable (X Y : Type) (f : X -> list Y).

  Fact flat_map_app l1 l2 : flat_map f (l1++l2) = flat_map f l1 ++ flat_map f l2.
  Proof.
      induction l1.
      +constructor.
      +simpl.
      rewrite IHl1.
      rewrite app_ass.
      trivial.
  Qed.

  Hypothesis Hf : forall x, f x <> nil.

  Fact flat_map_nil l : nil = flat_map f l -> l = nil.
  Proof.


(*
  intros H.
  induction l;auto.


1 subgoal
X, Y : Type
f : X -> list Y
Hf : forall x : X, f x <> nil
a : X
l : list X
H : nil = flat_map f (a :: l)
IHl : nil = flat_map f l -> l = nil
______________________________________(1/1)
a :: l = nil

*)
(*
intros H.
symmetry in H.
induction l;trivial. 
contradict H.
red.
red  in Hf.
intros H.
apply Hf with (x:=a).



1 subgoal
X, Y : Type
f : X -> list Y
Hf : forall x : X, f x = nil -> False
a : X
l : list X
IHl : flat_map f l = nil -> l = nil
H : flat_map f (a :: l) = nil
______________________________________(1/1)
f a = nil
*)


  Admitted.

End flat_map.

(** Definition of the notion of prefix 
    
        l is a prefix of l++r 
        
    which is denoted by l <p l++r
    together with a small library
*)

Definition prefix X (l ll : list X) := exists r, ll = l++r.
  
Infix "<p" := (@prefix _) (at level 70, no associativity).
  
Section prefix. (* as an inductive predicate *)
   
  Variable X : Type.
  
  Implicit Types (l ll : list X).
  
  Fact in_prefix_0 ll : nil <p ll.
  Proof. exists ll; auto. Qed.
  
  Fact in_prefix_1 x l ll : l <p ll -> x::l <p x::ll.
  Proof. intros (r & ?); subst; exists r; auto. Qed.

  Fact prefix_right l r : l <p l ++ r.
  Proof. exists r; auto. Qed.

  Fact prefix_length l m : l <p m -> length l <= length m.
  Proof. intros (? & ?); subst; rew length; omega. Qed.
  
  Fact prefix_app_lft l r1 r2 : r1 <p r2 -> l++r1 <p l++r2.
  Proof.
    intros (a & ?); subst.
    exists a; rewrite app_ass; auto.
  Qed.
  
  Fact prefix_inv x y l ll : x::l <p y::ll -> x = y /\ l <p ll.
  Proof.
    intros (r & Hr).
    inversion Hr; split; auto.
    exists r; auto.
  Qed.
  
  Fact prefix_list_inv l r rr : l++r <p l++rr -> r <p rr.
  Proof.
    induction l as [ | x l IHl ]; simpl; auto.
    intros H; apply prefix_inv, proj2, IHl in H; auto.
  Qed.

  Fact prefix_refl l : l <p l.
  Proof. exists nil; rewrite <- app_nil_end; auto. Qed.

  Fact prefix_trans l1 l2 l3 : l1 <p l2 -> l2 <p l3 -> l1 <p l3.
  Proof. intros (m1 & H1) (m2 & H2); subst; exists (m1++m2); rewrite app_ass; auto. Qed.

  Section prefix_rect.

    Variables (P : list X -> list X -> Type)
              (HP0 : forall ll, P nil ll)
              (HP1 : forall x l ll, l <p ll -> P l ll -> P (x::l) (x::ll)).
              
    Definition prefix_rect l ll : l <p ll -> P l ll.
    Proof.
      revert l; induction ll as [ | x ll IHll ]; intros l H.
      
      replace l with (nil : list X).
      apply HP0.
      destruct H as (r & Hr).
      destruct l; auto; discriminate.
      
      destruct l as [ | y l ].
      apply HP0.
      apply prefix_inv in H.
      destruct H as (? & E); subst y.
      apply HP1; [ | apply IHll ]; trivial.
    Qed.
   
  End prefix_rect.

  Fact prefix_app_inv l1 l2 r1 r2 : l1++l2 <p r1++r2 -> { l1 <p r1 } + { r1 <p l1 }.
  Proof.
    revert l2 r1 r2; induction l1 as [ | x l1 IH ]; intros l2 r1 r2.
    +intros H.
    left.
    apply in_prefix_0.
    +destruct r1 as [| y r1].
    intros H;right;apply in_prefix_0.    
    simpl; intros H; apply prefix_inv in H.
        
    destruct H as (E & H); subst y.
    destruct IH with (1 := H); [ left | right ];
    apply in_prefix_1; auto.

  Qed.
  
End prefix.

Definition prefix_spec X (l ll : list X) : l <p ll -> { r | ll = l ++ r }.
Proof.
  induction 1 as [ ll | x l ll _ (r & Hr) ] using prefix_rect.
  exists ll. 
  trivial.
  exists r.
  subst.
  simpl.
  trivial.
Qed.

Fact prefix_app_lft_inv X (l1 l2 m : list X) : l1++l2 <p m -> { m2 | m = l1++m2 /\ l2 <p m2 }.
Proof.

  intros H.
  apply prefix_spec in H.
  destruct H as (r & H).
  exists (l2++r); simpl; split.
  rewrite app_assoc.
  trivial.
  exists r.
  trivial.
Qed.

(** Binary trees *)

Inductive bt : Set := bt0 | bt1 : bt -> bt -> bt.

Delimit Scope bt_scope with bt.

Notation null := bt0.    (* typing that is easier *)
Notation ø := bt0.       (* for a nicer display *)

Notation " '<<' x ',' y '>>' " := (bt1 x y) (at level 0): bt_scope.
Notation " ⟨ x , y ⟩ " := (bt1 x y) (at level 0): bt_scope.

Reserved Notation "〈 t 〉" (at level 0, no associativity).
Reserved Notation " '[[' t ']]' " (at level 0, no associativity).

Open Scope bt_scope.

(* We can decide if two trees are equal or not *)

Definition bt_eq_dec (s t : bt) : { s = t } + { s <> t }.
Proof.
  revert t; induction s as [ | a Ha b Hb ]; intros [ | c d ].
  +left;trivial.
  +right;discriminate.
  +right;discriminate.
  +decide equality.

  Qed.

Fact bt_pair_neq a1 b1 a2 b2 : <<a1,a2>> <> <<b1,b2>> -> { a1 <> b1 } + { a2 <> b2 }.
Proof.


constructor.
(*
1 subgoal
a1, b1, a2, b2 : bt
H : ⟨ a1, a2 ⟩ <> ⟨ b1, b2 ⟩
______________________________________(1/1)
a1 <> b1
*)
red.
intros H1.
apply H.
(*
1 subgoal
a1, b1, a2, b2 : bt
H : ⟨ a1, a2 ⟩ <> ⟨ b1, b2 ⟩
H1 : a1 = b1
______________________________________(1/1)
⟨ a1, a2 ⟩ = ⟨ b1, b2 ⟩

*)


Admitted. 

Inductive bt_mirror : bt -> bt -> Prop :=
  | in_bt_mirror_0 : bt_mirror ø ø
  | in_bt_mirror_1 : forall a b c d, bt_mirror a b 
                                  -> bt_mirror c d
                                  -> bt_mirror <<a,c>> <<d,b>>.

Definition bt_compute_mirror s : { t | bt_mirror s t }.
Proof.
(*
exists s.
induction s;constructor.

(*
2 subgoals
s1, s2 : bt
IHs1 : bt_mirror s1 s1
IHs2 : bt_mirror s2 s2
______________________________________(1/2)
bt_mirror s1 s2
______________________________________(2/2)
bt_mirror s2 s1

*)
*)
induction s.
exists null.
constructor.
exists⟨ s1, s2 ⟩.
constructor.
(*elim IHs1.*)
(*
2 subgoals
s1, s2 : bt
IHs1 : {t : bt | bt_mirror s1 t}
IHs2 : {t : bt | bt_mirror s2 t}
______________________________________(1/2)
bt_mirror s1 s2
______________________________________(2/2)
bt_mirror s2 s1

*)
Admitted.

Fixpoint bt_size t :=
  match t with 
    | ø         => 1
    | <<t1,t2>> => 1 + 〈 t1 〉 + 〈 t2 〉
  end
where "〈 t 〉" := (bt_size t).

Fact bt_mirror_size s t : bt_mirror s t -> 〈 s 〉 = 〈 t 〉.
Proof.
(*
intros H.
induction 〈 s 〉;induction 〈 t 〉;auto.


3 subgoals
s, t : bt
H : bt_mirror s t
n : nat
IHn : 0 = n
______________________________________(1/3)
0 = S n
______________________________________(2/3)
S n = 0
______________________________________(3/3)
S n = S n0


*)

Admitted.

(* Encoding of binary trees as list of Zero and One *)

Notation Zero := false.
Notation One  := true.

Fixpoint bt_bin t : list bool :=
  match t with
    | ø       => Zero :: nil
    | <<a,b>> => One :: [[a]] ++ [[b]]
  end
where "[[ t ]]" := (bt_bin t).

Eval compute in [[ <<ø,ø>> ]].
Eval compute in [[ <<ø,<<ø,ø>>>> ]].

Fact bt_bin_not_nil t : [[t]] <> nil.
Proof.
induction t.
discriminate.
discriminate.
Qed.

Hint Resolve bt_bin_not_nil.

(* The length of the encoding is the size of the tree *)

Fact bt_bin_length t : length [[t]] = 〈 t 〉.
Proof.
  induction t;trivial.
  replace (〈 ⟨ t1, t2 ⟩ 〉) with (1 + 〈 t1 〉 + 〈 t2 〉).
  simpl.
  rewrite app_length.
  auto.
  constructor.
Qed.



Fact bt_bin_length_geq t : 1 <= length [[t]].
Proof.
induction t;
simpl;auto.
rewrite app_length.
omega.
Qed.

(** The essential lemma of non-ambiguity: 
       
     if  [[s]] ++ l = [[t]] ++ m  then   s = t and l = m

*) 

Lemma bt_bin_eq s : forall t l m, [[s]] ++ l = [[t]] ++ m -> s = t /\ l = m. 
Proof.
  induction s as [ | s1 IH1 s2 IH2 ]; intros [ | t1 t2 ].
  intros l m H; split.
  trivial.
  +apply app_inv_head in H;trivial.
  +intros l m H;discriminate.
  +intros l m H;discriminate.
  +intros l m H.

(*
1 subgoal
s1, s2 : bt
IH1 : forall (t : bt) (l m : list bool),
      [[s1]] ++ l = [[t]] ++ m -> s1 = t /\ l = m
IH2 : forall (t : bt) (l m : list bool),
      [[s2]] ++ l = [[t]] ++ m -> s2 = t /\ l = m
t1, t2 : bt
l, m : list bool
H : [[⟨ s1, s2 ⟩]] ++ l = [[⟨ t1, t2 ⟩]] ++ m
______________________________________(1/1)
⟨ s1, s2 ⟩ = ⟨ t1, t2 ⟩ /\ l = m


idée :
  apply list_app_inj in H.
  destruct H.  
  split.


*)

  
(*
list_app_inj X (l1 l2 r1 r2 : list X) : length l1 = length l2 -> l1++r1 = l2++r2 -> l1 = l2 /\ r1 = r2.
Proof.

*)
  
  
  
Admitted.

Corollary bt_bin_prefix_eq s t : [[s]] <p [[t]] -> s = t.
Proof.
  intros (l & Hl).
  induction s;
  induction t;
  trivial.
  discriminate.
  discriminate.
  


  
  
Admitted.

Corollary bt_bin_inj s t : [[s]] = [[t]] -> s = t.
Proof.
replace ([[s]]) with (([[s]]++nil)).
  replace  ([[t]]) with (([[t]]++nil)).
  intros; apply bt_bin_eq in H ; destruct H.
  auto.
  apply app_nil_r.
  apply app_nil_r.
Qed.

Corollary bt_bin_prefix_app_eq s t l m : [[s]]++l <p [[t]]++m -> s = t /\ l <p m.
Proof.

intros H.
split.
induction s.
(*intros H.
split.
apply bt_bin_prefix_eq.
apply prefix_list_inv in H.*)
(*
apply prefix_app_inv in H.
destruct H;trivial.
contradict p.
simpl.*)
Admitted.

Corollary bt_bin_uniq ll t1 t2 : [[t1]] <p ll -> [[t2]] <p ll -> t1 = t2.
Proof.

intros H1 H2.

Admitted.

Lemma flat_map_bt_bin_eq lt1 : forall lt2 l m, 
     flat_map bt_bin lt1 ++ l = flat_map bt_bin lt2 ++ m
  -> { lt1 <p lt2 } + { lt2 <p lt1 }.
Proof. 
  induction lt1 as [ | t1 lt1 IH ]; intros lt2 l m E; 
    [ | destruct lt2 as [ | t2 lt2 ] ]; simpl in E.
+left.
apply in_prefix_0.
+right.
apply in_prefix_0.
+

Admitted.

(* [[[t1;...;tn]]] = [[t1]]++...++[[tn]] *)

Notation " '[[[' l ']]]' " := (flat_map bt_bin l) (at level 0, no associativity).

(* The encoding of a list of trees is unambiguous 

     if [[s1]]++...++[[sk]] = [[t1]]++...++[[tp]] then [s1,...,sk] = [t1,...,tp] 

*)

Theorem lbt_bin_inj lt1 lt2 : [[[lt1]]] = [[[lt2]]] -> lt1 = lt2.
Proof.
  intros H; generalize H; intros H1.
  rewrite (app_nil_end (_ _ lt2)), (app_nil_end (_ _ lt1)) in H.
  apply flat_map_bt_bin_eq in H.
  destruct H as [ (r & H) | (r & H) ]; subst; rewrite flat_map_app in H1.
  
Admitted.

(** Now the decoders, beware that bt_bin is injective but not surjective !!
    Indeed, no binary tree encodes into One :: nil for instance *)

(* Given a sequence of boolean value lb, either 

     1/ computes a prefix of lb which encodes some binary tree t
     2/ or show that no such tree exists.
*)


Definition bin_bt_dec (lb : list bool) : { t : bt & { r | lb = [[t]] ++ r } } 
                                       + { forall t, ~ [[t]] <p lb }.
Proof.
  induction on length of lb as [ [ | [] lb1 ] IH ].

  (* lb = nil *)
  
  right; intros [] (r & Hr); discriminate.

  (* lb = One :: lb1  >>>> call the induction hypothesis on lb1 (shorter than lb) *)

  destruct (IH lb1) as [ (t1 & lb2 & H1) | C ].
  induction lb1;
  auto.
 
  
  (* lb1 = [[t1]] ++ lb2  >>>> call the induction hypothesis on lb2 (shorter than lb1, and thus of lb) *)
  
  destruct (IH lb2) as [ (t2 & lb' & H2) | C ].
  induction lb2.
  
  
  admit.

  (* lb2 = [[t2]] ++ lb' *)
 
  admit.
   
  (* ~ [[t]] <p lb2 *)  
  
  admit.
  
  (* ~ [[t]] <p lb1,  *) 
  
  admit. 
 
  (* lb = Zero :: lb1 *)
  
  left; exists ø, lb1; simpl; auto.

Admitted.

(* Given a list of boolean values lb, computes a maximal list of trees [t1;...;tk]
   such that lb = [[t1]]++...++[[tk]]++r where r is not prefixed by a bt *)

Definition bin_lbt_decode (lb : list bool) : 
        { lt : _ &  { r | lb = [[[lt]]] ++ r /\ forall t, ~ [[t]] <p r } }.
Proof.
  induction on length of lb as [ lb IH ].
  destruct (bin_bt_dec lb) as [ (t & r & H) | H ].

Admitted.

(* lb is not of the form [[t]]++... for any t *)

Definition not_prefixed lb := forall t, ~ [[t]] <p lb.

Fact not_prefixed_0 : not_prefixed nil.
Proof. intros [] []; discriminate. Qed.

Fact not_prefixed_1 lb : ~ not_prefixed (Zero::lb).
Proof.
  intros H; apply (H ø); apply in_prefix_1, in_prefix_0.
Qed.

(* If One::lb is not prefix by a tree then
   either lb = [[t]]++r where r is not prefixed by a tree
   or lb is not prefixed *)

Fact not_prefixed_2 lb : 
        not_prefixed (One::lb) 
     -> { t : _ & { r | lb = [[t]]++r /\ not_prefixed r } } 
      + { not_prefixed lb }.
Proof.
  intros H.
  destruct (bin_bt_dec lb) as [ (t & r & H1) | H1 ].
  right.
  subst.
  (*

  left.
  exists t;exists r.
  split;auto.

  subst.
  apply H.
  admit.
  *)
  
Admitted.

(** However, every list which is not prefixed by a tree can be extended into (the encoding of) a tree *)

Theorem bin_bt_extend (lb : list bool) : (forall t, ~ [[t]] <p lb) -> { rb : _ & { t | lb ++ rb = [[t]] } }.
Proof.
  fold (not_prefixed lb).
  induction on length of lb as [ [ | [] lb ] IH ]; intros Hlb.
  
  admit.

  destruct (not_prefixed_2 Hlb) as [ (t & r & H1 & H2) | H1 ].
  admit.
  admit.
  
  exfalso; revert Hlb; apply not_prefixed_1.
Admitted.

(* Any sequence of 0s and 1s is the prefix of some encoded sequence of trees *)

Theorem bin_lbt_complete lb : { lt | lb <p [[[lt]]] }.
Proof.
  destruct (bin_lbt_decode lb) as (lt & r & H1 & H2).
  destruct (bin_bt_extend H2) as (rb & t & H3).
  exists (lt++t::nil), rb.
  rewrite H1, flat_map_app, app_ass; simpl.
  rewrite <- app_nil_end; f_equal; auto.
Qed.



