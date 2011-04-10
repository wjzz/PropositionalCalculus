Require Import Bool.
Require Import Bool.Bool.
Require Import Classical.

(* Some additional boolean operators (like negb, orb and addb). 

   They are introduced to improve readability and overall clearness. 
*)

Definition implb (b1 b2: bool) := orb  (negb b1) b2.
Definition iffb  (b1 b2: bool) := andb (implb b1 b2) (implb b2 b1).


(* A tactic for solving goals that only include boolean values.

   It just tries all the cases by destructing all variables,
   unfolding iffb and implb and finishing with tauto/discriminate 
*)

Ltac destruct_bools := 
  match goal with
  | [ |- forall A: bool, _ ] => destruct A; destruct_bools
  | [ |- _ ] => intros; try unfold iffb; try unfold implb; 
                simpl in *; discriminate || tauto
  | _ => idtac
  end.


(* Lemmas that are used in the logic file. *)

Lemma iffb_factor_out_both : forall b1 b2 b3 b4: bool,
  b1 <> b2 -> b3 <> b4 -> iffb b1 b3 = iffb b2 b4.
Proof.
  destruct_bools.
Qed.
  

Lemma iffb_factor_out_both2 : forall b1 b2 b3 b4: bool,
  b1 = b2 -> b3 = b4 -> iffb b1 b3 = iffb b2 b4.
Proof. 
  destruct_bools.
Qed.


Lemma iffb_ineq : forall b1 b2 b3 b4: bool,
  b1 <> b2 -> b3 = b4 -> iffb b1 b3 <> iffb b2 b4.
Proof.
  destruct_bools.
Qed.


Lemma iffb_ineq2 : forall b1 b2 b3 b4: bool,
  b1 = b2 -> b3 <> b4 -> iffb b1 b3 <> iffb b2 b4.
Proof.
  destruct_bools.
Qed.

Lemma double_ineq: forall a b c: bool, 
  a <> b -> b <> c -> a = c.
Proof.
  destruct_bools.
Qed.


Lemma negb_inj: forall b b1: bool, negb b <> negb b1 -> b <> b1.
Proof. 
  intros b b1 H. intro H0. apply H. rewrite H0; trivial. 
Qed.



(* Lemmas that we want to use with auto *)

Hint Resolve iffb_factor_out_both iffb_factor_out_both2 : iffb_base.
Hint Resolve iffb_ineq iffb_ineq2 : iffb_base.
Hint Resolve double_ineq : logic.



(* A boolean value has to be either true or false *)
(* Use classic and b <> false -> b=true *)

Lemma bool_cases: forall b: bool, b = true \/ b = false.
Proof. intros b.
  assert (b = true \/ ~ b = true) as H; try apply classic.
  elim H; intros; try tauto.
  right. apply not_true_is_false; trivial.
Qed.

Ltac by_casesb h := assert h by (apply bool_cases). 

