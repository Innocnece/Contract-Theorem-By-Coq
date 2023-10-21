Require Import Coq.Sets.Ensembles.
Require Import Coq.Logic.Epsilon.
Require Import Coq.Logic.Classical.


Notation "a ∈ A" := (In _ A a) (at level 10).
Notation "B ∪ C" := (Union _ B C) (at level 65, left associativity).
Notation "[ a ]" := (Singleton _ a)
                    (at level 0, right associativity).
Notation "A ⊆ B" := (Included _ A B) (at level 70).
Notation "A ~ B" := (Setminus _ A B)
                    (at level 0, right associativity).

(* 集合性质 *)
Corollary UnionI : forall {U} (a: U) B C, 
  a ∈ (B ∪ C) <-> a ∈ B \/ a ∈ C.
Proof. 
  split; intros; destruct H; eauto with sets. 
Qed.

Corollary Single : forall {U} (a x: U), a ∈ [ x ] <-> a = x.
Proof. split; intros. destruct H; auto. rewrite H. split. Qed.

Global Hint Resolve UnionI Single: sets.

Corollary commu : forall {U} (A B: Ensemble U), A ∪ B = B ∪ A.
Proof.
  intros. apply Extensionality_Ensembles; red; intros; 
  split; red; intros.
  - destruct H. right; auto. left;auto.
  - destruct H. right; auto. left;auto.
Qed.

Corollary assoc : forall {U} (A B C: Ensemble U), 
  A ∪ B ∪ C = A ∪ (B ∪ C).
Proof.
  intros. apply Extensionality_Ensembles; red; 
  intros; split; red; intros.
  - destruct H. 
    + destruct H. left. auto. right; left; auto.
    + right; right; auto.
  - destruct H.
    + left; left; auto.
    + destruct H. left; right; auto. right; auto.
Qed.

(* 逻辑性质 *)
(* 排中律 *)
Theorem excluded : forall p, {p} + {~p}.
Proof.
  intros. assert { x:bool | if x then p else ~p }.
  { apply constructive_indefinite_description.
    destruct (classic p).
    - exists true. auto.
    - exists false. auto. }
  destruct H,x; auto.
Qed.

(* (* Logic 库 *)*)
Theorem or_iff_compat : forall (A B C D: Prop),
  (A <-> B) /\ (C <-> D) -> (A \/ C <-> B \/ D).
Proof.
  intros. destruct H. split; intros. 
  destruct H1. try left; try apply H; auto. try right;
  try apply H0; auto. 
  destruct H1. try left; try apply H; auto. try right;
  try apply H0; auto.
Qed.
(* P71 3.2.1 基本语法 *)

(* 一阶语言符号 *)
(*个体变元*)
Inductive Var : Set :=
  | X : nat -> Var.

(*个体常元*)
Inductive Con : Set :=
  | C : nat -> Con.

(*运算符*)
(* Inductive Fun : Set :=
  | F : nat -> Fun. *)
  
Inductive Fun : Set :=
  | F : nat -> nat -> Fun.

(*谓词*)
(* Inductive Rel : Set :=
  | R : nat -> Rel. *)

Inductive Rel : Set :=
  | R : nat -> nat -> Rel.

(* 元数（arity）函数 *)
Definition arity_F (f : Fun) : nat :=
  match f with
  | F a b => a
  end.

Definition arity_R (r : Rel) : nat :=
  match r with
  | R a b => a
  end.

(* 项 *)
Inductive vector (A: Type) : nat -> Type :=
  |vector0 : vector A 0
  |vectorcons : forall (h:A) (n:nat), vector A n -> vector A (S n).

Inductive term : Set :=
  | Tvar : Var -> term
  | Tcon : Con -> term
  | Tfun : forall f: Fun, vector term (arity_F f) -> term.

Definition var_num (v: Var):=
  match v with
  | X n => n
  end.

Definition con_num (v: Con):=
  match v with
  | C n => n
  end.

(* 变元相关性质 *)
Fixpoint eqb (n m: nat) : bool :=
  match n with
  | 0 => match m with
         | 0 => true
         | S _ => false
         end
  | S n' => match m with
            | 0 => false
            | S m' => eqb n' m'
            end
  end.

Definition eqbv (n m: Var) : bool :=
  match n, m with
  | X p, X q => eqb p q
  end.

Corollary eq_n : forall n, eqb n n = true.
Proof.
  intros. induction n.
  - auto.
  - simpl. auto.
Qed.

Corollary eqbv_n : forall n, eqbv n n = true.
Proof.
  intros. induction n. simpl. apply eq_n.
Qed.

Corollary eqb_true : forall (m n: nat), eqb m n = true <-> m = n.
Proof.
  intros. split; intros. 
  - generalize dependent n. induction m; intros.
    + inversion H. destruct n; auto. discriminate H1.
    + inversion H. destruct n; auto. discriminate H.
  - rewrite H. apply eq_n.
Qed.

Corollary eqb_false : forall (m n: nat), eqb m n = false <-> m <> n.
Proof.
  intros. split; intros; generalize dependent n; induction m.
  - intros; inversion H; destruct n; auto.
    + discriminate H1.
  - intros. destruct n; intro; rewrite H0 in H;
    rewrite eq_n in H; inversion H.
  - intros. destruct n. assert(0 = 0). auto. apply H in H0. 
    inversion H0. simpl. auto.
  - intros. destruct n. 
    + simpl. auto.
    + simpl. apply IHm. intro. rewrite H0 in H. apply H. auto.
Qed.

Corollary eqbv_true : forall (m n: Var), eqbv m n = true <-> m = n.
Proof.
  intros. split; intros; destruct m; destruct n. 
  - simpl in H. f_equal. apply eqb_true. auto.
  - inversion H. simpl. apply eq_n.
Qed.

Corollary eqbv_fasle : forall (m n: Var), 
  eqbv m n = false <-> m <> n.
Proof.
  intros. split; intros; destruct m; destruct n.
  - simpl in H. intro. inversion H0.
    rewrite H2 in H.  rewrite eq_n in H. inversion H.
  - simpl. apply eqb_false. intro. apply H. congruence. 
Qed.

(* 常元相关性质 *)
Definition eqbc (n m: Con) : bool :=
  match n, m with
  | C p, C q => eqb p q
  end.
Corollary eqbc_n: forall (n:Con), eqbc n n =true.
Proof.
  intros. destruct n.
  simpl. apply eq_n.
Qed.

Corollary eqbc_true : forall (m n: Con), eqbc m n = true <-> m = n.
Proof.
  intros. split; intros; destruct m; destruct n. 
  - simpl in H. f_equal. apply eqb_true. auto.
  - inversion H. simpl. apply eq_n.
Qed.

Corollary eqbc_fasle : forall (m n: Con), 
  eqbc m n = false <-> m <> n.
Proof.
  intros. split; intros; destruct m; destruct n.
  - simpl in H. intro. inversion H0.
    rewrite H2 in H.  rewrite eq_n in H. inversion H.
  - simpl. apply eqb_false. intro. apply H. congruence. 
Qed.

(* 公式 *)
Section Formula.

Inductive Formula :=
  | equality : term -> term -> Formula
  | atomic : forall (r: Rel), vector (term) (arity_R r) -> Formula
  | Not : Formula -> Formula
  | Contain : Formula -> Formula -> Formula 
  | Forall : Var -> Formula -> Formula.

(* 其他符号 *)
Definition Inequality t1 t2 := Not (equality t1 t2). 
(* ∨ *)
Definition Disjunction p q := Contain (Not p) q.
(* ∧ *)
Definition Conjunction p q := Not (Contain p (Not q)).
(* ↔ *)
Definition Equivalent p q := Conjunction (Contain p q) (Contain q p).

Definition Exists x p := Not (Forall x (Not p)).

End Formula.


Notation "¬ q" := (Not q)(at level 5,right associativity).

Notation "p → q" := (Contain p q)
                    (at level 11,right associativity).

Notation "∀ x , p" := (Forall x p) 
                       (at level 7, right associativity).

Notation " p ∨ q " := (Disjunction p q)
                      (at level 11, right associativity).
 
Notation " p ∧ q " := (Conjunction p q)
                      (at level 9, right associativity).

Notation " p ↔ q " := (Equivalent p q)
                      (at level 12, right associativity).

Notation "∃ x , p" := (Exists x p)
                      (at level 8, right associativity).



(* 归纳证明 *)
(* 项的归纳函数 *)
Definition case0 {A} (P: vector A 0 -> Type) 
  (H: P (vector0 A)) v : P v :=
  match v with
  |vector0 _ => H
  |_ => fun devil => False_ind (@IDProp) devil
  end.

Definition caseS {A} (P: forall {n}, vector A (S n) -> Type)
  (H: forall h {n} t, @P n (vectorcons _ h _ t)) {n}
  (v: vector A (S n)) : P v :=
  match v with
  |vectorcons _ h _ t => H h t
  |_ => fun devil => False_ind (@IDProp) devil
  end.

Definition caseS' {A} {n: nat} (v: vector A (S n)) :
  forall (P: vector A (S n) -> Type)
  (H: forall h t, P (vectorcons _ h _ t)), P v :=
  match v with
  | vectorcons _ h _ t => fun P H => H h t
  | _ => fun devil => False_rect (@IDProp) devil
  end.

Notation "a :: l" := (vectorcons _ a _ l).

Section term_ind_process.

Variable P : term -> Prop.
Variable P0 : forall n, vector term n -> Prop.
Variable varcase : forall n, P (Tvar n).
Variable concase : forall n, P (Tcon n).
Variable nilcase : forall t, P0 0 t.
Variable applycase :
  forall (f: Fun) (v: vector term (arity_F f)), 
  P0 (arity_F f) v -> P (Tfun _ v).
Variable conscase : forall (n: nat) (t: term) (t0: vector term n),
  P t -> P0 n t0 -> P0 (S n) (t :: t0).

Fixpoint Term_ind_new (t: term) : P t :=
  let fix Terms_ind (n: nat) (vec: (vector term n)) 
  {struct vec} : P0 n vec:=
  match vec in (vector _ n) return (P0 n vec) with
  | vector0 _ => nilcase (vector0 _)
  | vectorcons _ t0 m ts =>
    conscase m t0 ts (Term_ind_new t0) (Terms_ind m ts)
  end in match t with
         | Tvar r => varcase r
         | Tcon r => concase r
         | Tfun f ts => applycase f ts (Terms_ind _ ts)
         end.

End term_ind_process.

(* 变元集 *) 
Definition Φ := @Empty_set Var.

Fixpoint term_Ens (t: term) :=
  match t with
  | Tcon c => Φ
  | Tvar x => [x]
  | Tfun  _ q => let fix Vector_Ens (n: nat) (r: vector (term) n) :=
                   match r with 
                   | vector0 _ => Φ 
                   | vectorcons _ h _ q => (term_Ens h) ∪ 
                                           (Vector_Ens _ q)
                   end in Vector_Ens _ q
  end. 

Fixpoint Vector_Ens (n: nat) (r: vector (term) n) :=
  match r with 
  | vector0 _ => Φ 
  | vectorcons _ h _ q => (term_Ens h) ∪ (Vector_Ens _ q)
  end.

(* 公式的变元集 *)
Fixpoint Formula_Ens (p: Formula) :=
  match p with 
  | equality t1 t2 => (term_Ens t1) ∪ (term_Ens t2)
  | atomic _ q => Vector_Ens _ q
  | Not q => Formula_Ens q
  | Contain m n =>  (Formula_Ens m) ∪ (Formula_Ens n)
  | Forall x q => (Formula_Ens q) ∪ [x]
  end.

(* 公式的自由变元集 *)
Fixpoint Formula_free_Ens (p: Formula) :=
  match p with 
  | equality t1 t2 => (term_Ens t1) ∪ (term_Ens t2)
  | atomic _ q => Vector_Ens _ q
  | Not q => Formula_free_Ens q
  | Contain m n => (Formula_free_Ens m) ∪ (Formula_free_Ens n)
  | Forall x q => (Formula_free_Ens q) ~ [x]
  end.

(* 公式的约束变元集 *)
Fixpoint Formula_bound_Ens (p: Formula) :=
  match p with 
  | equality t1 t2 => Φ
  | atomic _ q => Φ
  | Not q => Formula_bound_Ens q
  | Contain m n => (Formula_bound_Ens m) ∪ (Formula_bound_Ens n)
  | Forall x q => (Formula_bound_Ens q) ∪ [x]
  end.


(* 语义 *)
Section structure.

Variable M : Type.

Class I_type := {
  I_c : Con -> M;
  I_f : forall (f: Fun), vector M (arity_F f) -> M;
  I_r : forall (r: Rel), vector M (arity_R r) -> Prop 
}.

Variable I : I_type.

(* 赋值 *)
Definition value := Var -> M.

(* x重新赋值为m *)
Definition value_v (v: value) (x: Var) (m: M) := 
  fun (y: Var) => match (excluded (y = x)) with
                   | left _ => m
                   | right _ => v y
                  end.

(*项t的赋值*)
Definition map_vector {A} {B} (f: A -> B) : forall {n} 
  (v: vector A n), vector B n :=
  fix map_fix {n} (v: vector A n) : vector B n := 
    match v with
    | vector0 _ => vector0 _
    | vectorcons _ a _ v' => vectorcons _ (f a) _ (map_fix v')
    end.

Fixpoint value_term (v: value) (t: term) : M :=
  match t with
  | Tcon c => I_c c
  | Tvar s => v s
  | Tfun f q => I_f f (map_vector (value_term v) q)
  end.

(* 塔斯基语义 可满足关系 ⊨ *)
Fixpoint satisfy_R (v: value) (p: Formula) {struct p} : Prop :=
  match p with
  | equality t1 t2 => value_term v t1 = value_term v t2
  | atomic r v1 => I_r r (map_vector (value_term v) v1)
  | Not q => ~ satisfy_R v q
  | Contain q r => (~ satisfy_R v q) \/ (satisfy_R v r)
  | Forall x q => forall (m: M), satisfy_R (value_v v x m) q 
  end.

(* 合同 *)
(* 在项上合同 *)
Definition agreement_t (u v: value) t :=
  forall x, x ∈ (term_Ens t) -> u x = v x.
(* 在公式上合同 *)
Definition agreement_f (u v: value) p :=
  forall x, x ∈ (Formula_free_Ens p) -> u x = v x.

End structure.

(* 可满足定义 *)
(* p 可满足 *)
Definition satisfyable_Formula p := exists M I v,satisfy_R M I v p.

(* 合同 *)
(* 合同引理（1）*)
Definition agree_t t := forall M I u v,
  agreement_t M u v t -> value_term M I u t = value_term M I v t.

Definition agree_v (n: nat) (t: vector(term) n) :=
  forall M I u v, (forall x, x ∈ (Vector_Ens n t) -> u x = v x) ->
  map_vector (value_term M I u) t = map_vector (value_term M I v) t.

Lemma agree_1 : forall (n: Var), agree_t (Tvar n).
Proof.
  intros. red. intros. simpl. apply H. simpl. split.
Qed.

Lemma agree_2 : forall (n: Con), agree_t (Tcon n).
Proof.
  intros. red. intros. simpl. auto.
Qed.

Lemma agree_3 : forall (t0: vector term 0), agree_v 0 t0.
Proof.
  intros. red. intros. apply case0. set(fun t1 =>
  map_vector (value_term M I u) t1 = vector0 M). apply (case0 P).
  unfold P. simpl. auto. 
Qed. 

Lemma agree_4 : forall (f: Fun) (v: vector term (arity_F f)),
  agree_v (arity_F f) v -> agree_t (Tfun f v).
Proof.
  intros. red. intros. red in H. simpl. f_equal. apply H.
  intros. red in H0. apply H0. apply H1.
Qed.

Lemma agree_5 : forall (n: nat) (t0: term) (t1: vector term n),
  agree_t t0 -> agree_v n t1 -> agree_v (S n) (t0 :: t1).
Proof.
  intros. red. intros. simpl. unfold agree_t in H. f_equal. 
  apply H. red. intros. apply H1. simpl. left. auto.
  red in H0. apply H0. intros. apply H1. simpl. right. auto.
Qed.

Theorem agree_fact_1 : forall t, agree_t t.
Proof.
  intros. apply Term_ind_new with agree_v.
  - apply agree_1. 
  - apply agree_2.
  - apply agree_3.
  - apply agree_4.
  - apply agree_5.
Qed.

Lemma agree_6 : forall n v, agree_v n v.
Proof.
  red. intros. induction v.
  - apply agree_3. intros. destruct H0.
  - simpl. f_equal. apply agree_fact_1. red. intros. 
    apply H. simpl. left; auto. apply IHv. intros. apply H. 
    simpl. right; auto.
Qed.
(* 合同引理（2）*)
Theorem agree_fact_2 : forall M I p u v, 
  agreement_f M u v p -> (satisfy_R M I u p <-> satisfy_R M I v p).
Proof.
  intros M. induction p.  
  - split; intros; simpl in H0; red; red in H. 
    assert(value_term M I u t = value_term M I v t /\
    value_term M I u t0 = value_term M I v t0).
    { split; apply agree_fact_1; red; intros; apply H; simpl.
      left; auto. right; auto. } destruct H1; congruence.
    assert(value_term M I u t = value_term M I v t /\
    value_term M I u t0 = value_term M I v t0 ).
    { split; apply agree_fact_1; red; intros; apply H; simpl.
      left; auto. right; auto. } destruct H1; congruence.
  - split; intros; simpl; red in H0; pose proof(agree_6 _ v);
    red in H1; assert(map_vector (value_term M I u) v = 
    map_vector (value_term M I v0) v) by (apply H1;intros; 
    apply H; simpl; apply H2). rewrite H2 in H0. auto.
    rewrite <-H2 in H0. auto.
  - intros. assert(agreement_f M u v p). { 
    red. intros. apply H. simpl. auto. } apply IHp in H0. simpl. 
    apply not_iff_compat. auto.
  - simpl. intros. 
    assert(agreement_f M u v p1 /\ agreement_f M u v p2).
    { split;red; intros; apply H; simpl. left. auto. right. auto. }
    destruct H0. apply IHp1 in H0. apply IHp2 in H1. 
    apply or_iff_compat. split. apply not_iff_compat. auto. auto.
  - intros. simpl in H. assert(forall m, 
    agreement_f M (value_v M u v m) (value_v M v0 v m) p).
    { intros. red. intros. red in H. simpl in H. unfold value_v.
    destruct(excluded (x = v)). auto. apply H. unfold Setminus.
    split; auto. intro. assert(x = v) by (apply Single in H1;auto).
    contradiction. } simpl. split; intros; simpl; simpl in H1;
    intros; specialize H0 with m; specialize H1 with m;
    pose proof (IHp (value_v M u v m) (value_v M v0 v m) H0);
    destruct H2. apply H2. auto. apply H3. auto.
Qed.

Definition valid_p p := forall M I v, satisfy_R M I v p.

Lemma valid_formula_l : forall M m v x p, ~ x ∈ (Formula_free_Ens p) ->       agreement_f M v (value_v M v x m) p.
Proof.
  intros. red. intros. 
  destruct(excluded(x0 = x)) eqn:E. rewrite e in H0. contradiction.
  unfold value_v. rewrite E. auto.
Qed.
Theorem valid_formula_t : forall p x,
  ~ x ∈ (Formula_free_Ens p) -> valid_p (p → (∀ x , p)).
Proof.
  intros. red. intros. simpl. 
  destruct (excluded (satisfy_R M I v p)).
  right. intros. try auto. apply agree_fact_2 with (u:= v).
  apply predicate_valid_formula_l; auto. auto.
Qed.
