Require Import Bool.
Require Import Arith.
Require Import Arith.Even.
Require Import Classical.
Require Import Bool.Bool.

Print LoadPath.
Load Looleans.


(* *******************************************************)
(* Language of formulas *)

Definition Var := nat.

Definition truth_assigment := Var -> bool.

Inductive Formula :=
  | tt
  | ff
  | var  : Var -> Formula
  | not  : Formula -> Formula
  | and  : Formula -> Formula -> Formula
  | or   : Formula -> Formula -> Formula
  | impl : Formula -> Formula -> Formula
  | iff  : Formula -> Formula -> Formula.





(* Semantic function for formulas, denotational style *)
Fixpoint eval (fi: truth_assigment) (f: Formula) : bool :=
  match f with
  | tt        => true
  | ff        => false
  | var  n    => fi n
  | not  f    => negb  (eval fi f)
  | and  l r  => andb  (eval fi l) (eval fi r)
  | or   l r  => orb   (eval fi l) (eval fi r)
  | impl l r  => implb (eval fi l) (eval fi r)
  | iff  l r  => iffb  (eval fi l) (eval fi r)
  end. 

Definition tautology (form: Formula) := 
  forall fi:truth_assigment, eval fi form = true.




Ltac logic      := auto with logic.
Ltac prove_taut := unfold tautology; intro fi.

Lemma simple_taut: tautology tt.
Proof.
  prove_taut; trivial.
Qed.

Lemma tertium_non_datur: 
  forall p:Var, tautology (or (var p) (not (var p))).
Proof.
  intros p; prove_taut.
  simpl.
  destruct (fi p); trivial.
Qed.






(* Our first theorem: without negation and ff we can't define all boolean functions *)


Inductive no_negation_or_ff : Formula -> Prop :=
  | nn_tt   : no_negation_or_ff tt
  | nn_var  : forall n:Var, no_negation_or_ff (var n)
  | nn_and  : forall l r: Formula, no_negation_or_ff l -> no_negation_or_ff r -> no_negation_or_ff (and  l r)
  | nn_or   : forall l r: Formula, no_negation_or_ff l -> no_negation_or_ff r -> no_negation_or_ff (or   l r)
  | nn_impl : forall l r: Formula, no_negation_or_ff l -> no_negation_or_ff r -> no_negation_or_ff (impl l r)
  | nn_iff  : forall l r: Formula, no_negation_or_ff l -> no_negation_or_ff r -> no_negation_or_ff (iff  l r).


Lemma positive_if_all_positive: forall (form: Formula) (fi: truth_assigment),
  no_negation_or_ff form -> (forall n:nat, fi n = true) -> eval fi form = true.
Proof.
  intros form fi no_neg const_form.
  induction form; 
  try (simpl; apply const_form); 
  try (inversion no_neg; fail); auto;
  try (simpl; inversion no_neg; clear H H0 l r; rewrite IHform1; auto).
  simpl.
  rewrite IHform2; auto.
Qed.

Theorem not_functionally_complete: 
  forall (v: Var) (f: Formula), 
  exists fi: truth_assigment,
  no_negation_or_ff f -> ~ tautology (iff (not (var v)) f).
Proof.
  intros v f.
  set (all_positive := (fun n:nat => true)).
  exists (all_positive).
  intro no_neg.
  intro.
  unfold tautology in H.
  assert (eval all_positive f = true).
  apply positive_if_all_positive; auto.
  (* if    f --> true   then   ~_|_ <=> f ---> true *)
  set (H1 := H all_positive).  
  simpl in H1.
  rewrite H0 in H1.
  discriminate H1.
Qed.





(* Our second result: a formula with only tt, var and iff cannot be
   equivalent to 'p or q' *)

Inductive only_iff_bottom_and_vars: Formula -> Prop :=
  | ifb_ff  : 
        only_iff_bottom_and_vars ff
  | ifb_var : 
        forall v: Var, only_iff_bottom_and_vars (var v)
  | ifb_iff : 
        forall f g: Formula, 
           only_iff_bottom_and_vars f -> 
           only_iff_bottom_and_vars g ->
           only_iff_bottom_and_vars (iff f g).


Fixpoint count_var (form: Formula) (v: Var) :=
  match form with
  | tt       => 0
  | ff       => 0
  | var  v2  => if beq_nat v v2 then 1 else 0
  | not  f   => count_var f v
  | and  f g => count_var f v + count_var g v
  | or   f g => count_var f v + count_var g v
  | impl f g => count_var f v + count_var g v
  | iff  f g => count_var f v + count_var g v
  end.


Lemma beq_nat_false2 : forall x y:nat, x <> y -> beq_nat x y = false.
Proof.
  apply beq_nat_false_iff.
Qed.

Hint Resolve beq_nat_false    : logic.
Hint Resolve beq_nat_true     : logic.
Hint Resolve beq_nat_false2   : logic.
Hint Resolve no_fixpoint_negb : logic.

Hint Rewrite andb_true_r : logic.
Hint Rewrite orb_false_r : logic.

Ltac kill_negb :=
  match goal with
  | [ |- ?X <> negb ?X ] => let h := fresh "H" in 
   (intro h; symmetry in h; generalize h; apply no_fixpoint_negb)
  end.

Ltac no_other_way := 
  match goal with
  | [ H: (match ?B with true => ?X | false => ?Y end = ?X) |- _] => 
    let x := fresh "L" in  (assert (x:B=true) by (destruct B; [trivial | discriminate])); clear H
  | [ H: (match ?B with true => ?X | false => ?Y end = ?Y) |- _] => 
    let x := fresh "L" in  (assert (x:B=false) by (destruct B; [discriminate | trivial])); clear H
  | _ => idtac "not found"
  end.


Lemma diff_vars: forall v v2: Var, count_var (var v2) v = 0 -> v <> v2.
Proof.
  intros v v2 H; simpl in H.
  no_other_way.
  auto with logic.
Qed.

Lemma same_vars: forall v v2: Var, count_var (var v2) v = 1 -> v = v2.
Proof.
  intros v v2 H; simpl in H.
  no_other_way. 
  auto with logic.
Qed.





(* A function that fixes (= negates) the value at the given point
   of the given truth_assigment *)

Definition fix_on_v (v: Var) (fi: truth_assigment) (v2: Var) :=
  if beq_nat v v2 then negb (fi v) else fi v2.

Lemma fix_on_others: forall v v2: Var, forall fi:truth_assigment,
  ~v = v2 -> fi v2 = fix_on_v v fi v2.
Proof.
  intros v v2 fi H.
  unfold fix_on_v.
  assert (beq_nat v v2 = false).
  auto with logic.
  rewrite H0; trivial.
Qed.

Lemma fix_on_same : forall v: Var, forall fi:truth_assigment,
  fi v = negb (fix_on_v v fi v).
Proof. 
  intros v fi.
  simpl. unfold fix_on_v.
  assert (beq_nat v v = true).
  induction v; simpl; try congruence; trivial.
  rewrite H.
  auto with logic.
  rewrite negb_involutive.
  auto.
Qed.

Lemma fix_on_same2 : forall v: Var, forall fi:truth_assigment,
  negb (fi v) = fix_on_v v fi v.
Proof. 
  intros v fi.
  simpl. unfold fix_on_v.
  assert (beq_nat v v = true).
  induction v; simpl; try congruence; trivial.
  rewrite H.
  auto with logic.
Qed.

Hint Resolve fix_on_others : logic.
Hint Resolve diff_vars : logic.


(* Two theorems that make it possible to prove the cant_express_or theorem. *)

Theorem both_cases:
  forall (f: Formula) (v: Var) (fi: truth_assigment),
    only_iff_bottom_and_vars f ->
   (even (count_var f v) ->  
    eval fi f = eval (fix_on_v v fi) f) /\
   (odd (count_var f v) -> 
    eval fi f <> eval (fix_on_v v fi) f).
Proof. 
  intros f v fi.
  intros H.
  induction H.

  (* ff case *)
  split; simpl; intros H; auto; inversion H.

  (* var v case *)
  split; simpl; intros H;

  case_eq (beq_nat v v0); intros H0.
  rewrite H0 in H; inversion H. inversion H2.
  apply fix_on_others. apply beq_nat_false; assumption.

  unfold fix_on_v. rewrite H0. assert (v = v0). apply beq_nat_true; auto.

  subst. auto with logic.
  rewrite H0 in H. inversion H.


  (* iff f g case *)
  destruct IHonly_iff_bottom_and_vars1;
  destruct IHonly_iff_bottom_and_vars2;
  split;

  intros Heven; simpl in Heven; 
  [apply even_plus_split in Heven | apply odd_plus_split in Heven];
  destruct Heven; simpl; destruct H5;
  auto with iffb_base.
Qed.


(* It's more convenient to split both cases *)

Theorem even_case: 
 forall (f: Formula) (v: Var) (fi: truth_assigment),
  even (count_var f v) -> 
  only_iff_bottom_and_vars f -> 
  eval fi f = eval (fix_on_v v fi) f.
Proof. 
  intros; apply both_cases; trivial. 
Qed.

Theorem odd_case: 
 forall (f: Formula) (v: Var) (fi: truth_assigment),
  odd (count_var f v) -> 
  only_iff_bottom_and_vars f -> 
  eval fi f <> eval (fix_on_v v fi) f.
Proof. 
  intros; apply both_cases; trivial. 
Qed.



(* The main goal/result of this script *)

Definition f0 := or (var 0) (var 1).

Theorem cant_express_or: 
  forall f:Formula, 
  only_iff_bottom_and_vars f ->
  exists fi:truth_assigment, eval fi f <> eval fi f0.
Proof.
  intros f H.
  set (a := count_var f 0) ;
  set (b := count_var f 1) ;
  set (H1 := even_or_odd a) ;
  set (H2 := even_or_odd b).
  elim H1 ;  elim H2 ; intros H3 H4; clear H1 H2.

  (* even a; even b; *)
  set (pi := fun (_:Var) => true).

  (* prove that a bool must be either true or false ... *)
  by_casesb (eval pi f = true \/ eval pi f = false). 

  elim H0; intro H2; clear H0.
  set (pi2 := fix_on_v 0 (fix_on_v 1 pi)).
  exists pi2.
  simpl.
  unfold pi2.
  rewrite <- fix_on_others with (v := 0); trivial.
  change (fix_on_v 1 pi 1) with (negb (pi 1)).
  rewrite <- even_case with (v := 0); auto.
  rewrite <- even_case with (v := 1); auto.
  simpl.
  rewrite H2; auto with logic.
  apply (diff_true_false).
  exists pi.
  simpl.
  rewrite H2; auto with logic.

  (* even a; odd b; *)
  set (pi := fun v:Var => match v with 0 => true | _ => false end).

  (* prove that a bool must be either true or false ... *)
  assert (H0: eval pi f = true \/ eval pi f = false) by (apply bool_cases).

  elim H0; intros H1; clear H0.
  set (pi2 := fix_on_v 0 pi).
  exists pi2.
  simpl.
  unfold pi2.
  rewrite <- even_case with (v := 0).
  rewrite H1.
  rewrite <- fix_on_others. simpl. apply diff_true_false. trivial. auto.
  auto.
  
  exists pi.
  simpl.
  rewrite H1; auto with logic.

  (* odd a; even b *)

  set (pi := fun v:Var => match v with 1 => true | _ => false end).

  (* prove that a bool must be either true or false ... *)
  assert (eval pi f = true \/ eval pi f = false) by (apply bool_cases).

  elim H0; intros H1; clear H0.
  set (pi2 := fix_on_v 1 pi).
  exists pi2.
  simpl.
  unfold pi2.
  rewrite <- even_case with (v := 1).
  rewrite H1.
  rewrite <- fix_on_same2. simpl. apply diff_true_false. trivial.
  auto.
  
  exists pi.
  simpl.
  rewrite H1; auto with logic.

  (* odd a; odd b *)
  set (pi := fun (_:Var) => true).

  assert (H0: eval pi f = true \/ eval pi f = false) by (apply bool_cases).

  elim H0; intro H2; clear H0.
  set (pi2 := fix_on_v 0 (fix_on_v 1 pi)).
  exists pi2.
  simpl.
  unfold pi2.
  rewrite <- fix_on_others with (v := 0); auto.
  change (fix_on_v 1 pi 1) with (negb (pi 1)).
  simpl.
  assert (eval (fix_on_v 0 (fix_on_v 1 pi)) f = true).
  assert (eval (fix_on_v 1 pi) f <> eval (fix_on_v 0 (fix_on_v 1 pi)) f);
    try (apply odd_case; auto).
  assert (eval pi f <> eval (fix_on_v 1 pi) f);
    try (apply odd_case; auto).
  eauto with logic.
  rewrite H0; auto with bool.
  exists pi.
  simpl.
  rewrite H2; auto with logic.
Qed.
