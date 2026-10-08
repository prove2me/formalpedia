-- Prove2me | Theorems.Thm_NegativeDP_Stationary_theorem43
-- name    : NegativeDP.Stationary.theorem43
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:54:31.874252+00:00
-- url     : https://prove2.me/theorems/f9868a2f-41ae-414f-8a31-f647138dee27
-- title:
--   Theorem 4.3 (N) — a semi-Markov policy dominates any policy, and a Markov policy dominates it in p-average
-- statement:
--   In the negative dynamic programming problem, let $\pi$ be any policy and $p$ a probability measure on $S$. Then there exist a (non-random) semi-Markov policy $\tau$ and a (non-random) Markov policy $\sigma$ such that
--
--   $$I(\tau)\ \ge\ I(\pi)\quad\text{at every state},\qquad pI(\sigma)\ \ge\ pI(\pi).$$
--
--   Thus non-random policies that remember only the initial and the current state dominate every policy, and non-random Markov policies dominate on average. The paper states the theorem for the discounted and negative cases; this item is the negative case. Theorem 8.3 begins by replacing an optimal policy by a semi-Markov one through this theorem.
--
--   **Formalization Note.** Semi-Markov means that the $n$th action is $g_n(s_1,s_n)$ for Borel maps $g_n:S\times S\to A$; Markov means it is $f_n(s_n)$ for Borel $f_n:S\to A$. The competitor $\pi$ is any randomized history-dependent plan. $pI=\int I\,dp$ is computed as $-\int(-I)\,dp$.
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966), p. 877, Theorem 4.3 (N)

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_NegativeDP_Stationary_Model
open MeasureTheory ProbabilityTheory Filter Topology
open DiscountedDP.Stationary (Hist Plan MarkovPlan MarkovPlan.toPlan stationary)

namespace NegativeDP.Stationary

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- Theorem 4.3, case N (p. 877): for any policy `π` and `p ∈ P(S)` there are a semi-Markov `τ`
and a Markov `σ` with `I(τ) ≥ I(π)` and `pI(σ) ≥ pI(π)`. -/
theorem theorem43 (P : Problem S A) (π : Plan (S := S) (A := A))
    (p : Measure S) [IsProbabilityMeasure p] :
    ∃ τ σ : Plan (S := S) (A := A), IsSemiMarkov τ ∧ IsMarkov σ ∧
      (∀ s, I P π s ≤ I P τ s) ∧ pInt p (I P π) ≤ pInt p (I P σ) := by sorry

end NegativeDP.Stationary
