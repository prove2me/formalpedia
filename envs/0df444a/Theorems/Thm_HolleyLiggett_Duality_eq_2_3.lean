-- Prove2me | Theorems.Thm_HolleyLiggett_Duality_eq_2_3
-- name    : HolleyLiggett.Duality.eq_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T09:40:23.718307+00:00
-- url     : https://prove2.me/theorems/964a0d50-7d46-44e4-bd33-9c0e3e3c7b4a
-- title:
--   (2.3), p. 647 — one step of the proximity process: P_η(η₁ ∈ B(F)) = Σ′ ∏_{i∈F} f_i(k_i) over N_{i,k_i} ∩ C(η) = ∅
-- statement:
--   Let $\eta_n$ be the discrete-time proximity process determined by the finite sets $\{N_{i,k}\}$ (with $N_{i,0}=\emptyset$) and the probability distributions $\{f_i\}$ on a countable site set $I$. For every configuration $\eta\in S$ and every finite set $F\subset I$,
--   $$P_\eta(\eta_1\in B(F))=\sum{}'\prod_{i\in F}f_i(k_i),$$
--   where $\sum'$ runs over those sequences $(k_i)_{i\in F}$ of nonnegative integers for which $N_{i,k_i}\cap C(\eta)=\emptyset$ for every $i\in F$.
--
--   This is the case $n=1$ of the duality theorem on the proximity side: the probability that every site of $F$ is vacant after one step.
--
--   **Formalization Note.** $P_\eta(\eta_1\in\cdot)$ is the time-1 law of the chain, i.e. the bind of the point mass at $\eta$ with the kernel (1.1). The sum is an unconditional sum in $[0,\infty]$ over all functions $F\to\mathbb N$, with the summand set to $0$ outside the stated sequences.
-- source:
--   Holley and Liggett, Ergodic theorems for weakly interacting infinite systems and the voter model, Ann. Probab. 3 (1975), p. 647, (2.3)

import Mathlib
import Definitions.Def_HolleyLiggett_Duality_Setting

namespace HolleyLiggett.Duality

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

open Classical in
/-- (2.3): `P_η(η_1 ∈ B(F)) = Σ′ ∏_{i∈F} f_i(k_i)`, the sum over the sequences `(k_i)_{i∈F}`
with `N_{i,k_i} ∩ C(η) = ∅` for every `i ∈ F`. -/
theorem eq_2_3 {I : Type*} [Countable I] [DecidableEq I] (N : I → ℕ → Finset I)
    (hN0 : ∀ i, N i 0 = ∅) (f : I → PMF ℕ)
    (η : Config I) (F : Finset I) :
    proxLaw N f η 1 (zeroOn F) =
      ∑' k : (↥F → ℕ),
        (if ∀ i : ↥F, Disjoint (N i (k i) : Set I) (occupied η) then ∏ i : ↥F, f i (k i) else 0) := by sorry

end HolleyLiggett.Duality
