-- Prove2me | Theorems.Thm_NegativeDP_Stationary_theorem42
-- name    : NegativeDP.Stationary.theorem42
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:54:31.16398+00:00
-- url     : https://prove2.me/theorems/7e43b4d0-9ec1-4085-913a-4d4c71b82e67
-- title:
--   Theorem 4.2 (N) — if switching from π to σ after n stages beats σ for all large n, then π beats σ
-- statement:
--   In the negative dynamic programming problem, let $\pi$ and $\sigma$ be policies, and let $\pi^n\sigma=(\pi_1,\dots,\pi_n,\sigma_{n+1},\dots)$ be the policy that follows $\pi$ for $n$ stages and then switches to $\sigma$. If there is $n_0$ such that
--
--   $$I(\pi^n\sigma)\ \ge\ I(\sigma)\quad\text{at every state, for all } n\ge n_0,$$
--
--   then $I(\pi)\ge I(\sigma)$ at every state.
--
--   In words: if it is better to use $\pi$ for $n$ stages and then switch to $\sigma$ than to use $\sigma$ from the beginning, for all large $n$, then it is better to use $\pi$ forever. The paper states the theorem for the discounted and negative cases (it may fail in the positive case, Example 4.2); this item is the negative case. It drives the stage-by-stage improvement in Theorem 4.3.
--
--   **Formalization Note.** Lean decisions are numbered from $0$, so `switchAt π n σ` takes decisions $0,\dots,n-1$ from $\pi$ and the later ones from $\sigma$, which reads the full history.
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966), p. 877, Theorem 4.2 (N)

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_NegativeDP_Stationary_Model
open MeasureTheory ProbabilityTheory Filter Topology
open DiscountedDP.Stationary (Hist Plan MarkovPlan MarkovPlan.toPlan stationary)

namespace NegativeDP.Stationary

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- Theorem 4.2, case N (p. 877): if `I(π^nσ) ≥ I(σ)` for all `n ≥ n₀`, then `I(π) ≥ I(σ)`. -/
theorem theorem42 (P : Problem S A) (π σ : Plan (S := S) (A := A))
    (h : ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ s, I P σ s ≤ I P (switchAt π n σ) s) :
    ∀ s, I P σ s ≤ I P π s := by sorry

end NegativeDP.Stationary
