-- Prove2me | Theorems.Thm_KellyStochasticNetworks_CountableReversal_markov_iff_past_future
-- name    : KellyStochasticNetworks.CountableReversal.markov_iff_past_future
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:45:49.958978+00:00
-- url     : https://prove2.me/theorems/8ce3d1fd-fa5d-491e-89e3-bf178dc12924
-- title:
--   Exercise 1.3 — Markovianity and conditional independence
-- statement:
--   Let $X(t)$, $t\in\mathbb R$, be measurable random variables on a common probability space, taking values in a countable discrete measurable state space. Its Markov property says that, conditional on a finite increasing history ending in $X(s)=j$ with positive probability, the probability of $X(u)=k$, $u>s$, depends only on $X(s)=j$.
--
--   This property is equivalent to the following: for every pair of finite increasing lists of times $a_1<\cdots<a_m<s<b_1<\cdots<b_n$, state assignments $x_i,y_i$, and state $j$ with $P(X(s)=j)>0$, writing $A=\{X(a_i)=x_i\text{ for every }i\}$ and $B=\{X(b_i)=y_i\text{ for every }i\}$,
--   $$
--   P(A\cap B\mid X(s)=j)=P(B\mid X(s)=j)P(A\mid X(s)=j).
--   $$
--   Thus past and future are conditionally independent given the present. The equivalence, including its converse, expresses the time symmetry needed for reversal.
--
--   **Formalization Note** Finite histories use `Fin n`, including empty histories. Conditional probabilities are event-probability ratios with the appropriate positive conditioning event. Markovianity here means the finite-history conditional-law property, independently of time homogeneity, path regularity, or transition rates.
-- source:
--   Kelly & Yudovina, Stochastic Networks (2014), supplied Lecture Notes PDF, printed p. 16 (PDF p. 24), Exercise 1.3; https://doi.org/10.1017/CBO9781139565363

import Mathlib

open MeasureTheory

namespace KellyStochasticNetworks.CountableReversal

theorem markov_iff_past_future {Ω S : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → S) (hX : ∀ t, Measurable (X t)) :
    let E := fun (t : ℝ) (j : S) =>
      (⟨{ω | X t ω = j}, hX t (measurableSet_singleton j)⟩ :
        {A : Set Ω // MeasurableSet A})
    let C := fun (n : ℕ) (t : Fin n → ℝ) (x : Fin n → S) =>
      (⟨{ω | ∀ i, X (t i) ω = x i}, by
        simpa only [Set.ofPred_forall, Set.preimage, Set.mem_singleton_iff] using
          MeasurableSet.iInter (fun i => hX (t i) (measurableSet_singleton (x i)))⟩ :
        {A : Set Ω // MeasurableSet A})
    let inter := fun (A B : {A : Set Ω // MeasurableSet A}) =>
      (⟨A.1 ∩ B.1, A.2.inter B.2⟩ : {A : Set Ω // MeasurableSet A})
    let cp := fun (A B : {A : Set Ω // MeasurableSet A}) =>
      (P (A.1 ∩ B.1)).toReal / (P B.1).toReal
    (∀ (n : ℕ) (t : Fin n → ℝ) (x : Fin n → S) (s u : ℝ) (j k : S),
      StrictMono t → (∀ i, t i < s) → s < u →
      0 < (P (inter (C n t x) (E s j)).1).toReal →
      cp (E u k) (inter (C n t x) (E s j)) = cp (E u k) (E s j)) ↔
    (∀ (m n : ℕ) (a : Fin m → ℝ) (b : Fin n → ℝ)
      (x : Fin m → S) (y : Fin n → S) (s : ℝ) (j : S),
      StrictMono a → StrictMono b → (∀ i, a i < s) → (∀ i, s < b i) →
      0 < (P (E s j).1).toReal →
      cp (inter (C m a x) (C n b y)) (E s j) =
        cp (C n b y) (E s j) * cp (C m a x) (E s j)) := by sorry

end KellyStochasticNetworks.CountableReversal
