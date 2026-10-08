-- Prove2me | Theorems.Thm_HolleyLiggett_Duality_eq_2_4
-- name    : HolleyLiggett.Duality.eq_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:42:43.857411+00:00
-- url     : https://prove2.me/theorems/e6730f93-c16a-4860-87e7-7c17228b0eab
-- title:
--   (2.4), p. 647 — one step of the b.p.i.: P_F(A₁ ∩ C(η) = ∅) = Σ′ ∏_{i∈F} f_i(k_i) over N_{i,k_i} ∩ C(η) = ∅
-- statement:
--   Let $A_n$ be the discrete-time branching process with interference determined by the finite sets $\{N_{i,k}\}$ (with $N_{i,0}=\emptyset$) and the distributions $\{f_i\}$ on a countable site set $I$. For every configuration $\eta\in S$ and every finite set $F\subset I$,
--   $$P_F(A_1\cap C(\eta)=\emptyset)=\sum{}'\prod_{i\in F}f_i(k_i),$$
--   where $\sum'$ runs over the same sequences as in (2.3): those $(k_i)_{i\in F}$ with $N_{i,k_i}\cap C(\eta)=\emptyset$ for every $i\in F$.
--
--   Together with (2.3) this proves the duality relation (1.7) for $n=1$.
--
--   **Formalization Note.** $P_F(A_1\cap C(\eta)=\emptyset)=\sum_{B}P_F(A_1=B)\,\mathbf 1[B\cap C(\eta)=\emptyset]$ with the one-step probabilities $P_F(A_1=B)$ of the chain with transition function (1.4). The right side is written out in full, not by reference to (2.3).
-- source:
--   Holley and Liggett, Ergodic theorems for weakly interacting infinite systems and the voter model, Ann. Probab. 3 (1975), p. 647, (2.4)

import Mathlib
import Definitions.Def_HolleyLiggett_Duality_Setting

namespace HolleyLiggett.Duality

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open Classical in
/-- (2.4): `P_F(A_1 ∩ C(η) = ∅) = Σ′ ∏_{i∈F} f_i(k_i)`, the sum over the same sequences as in (2.3). -/
theorem eq_2_4 {I : Type*} [Countable I] [DecidableEq I] (N : I → ℕ → Finset I)
    (hN0 : ∀ i, N i 0 = ∅) (f : I → PMF ℕ)
    (η : Config I) (F : Finset I) :
    dualProb N f 1 F η =
      ∑' k : (↥F → ℕ),
        (if ∀ i : ↥F, Disjoint (N i (k i) : Set I) (occupied η) then ∏ i : ↥F, f i (k i) else 0) := by sorry

end HolleyLiggett.Duality
