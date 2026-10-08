-- Prove2me | Theorems.Thm_NegativeDP_OptEq_theorem52e
-- name    : NegativeDP.OptEq.theorem52e
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:53:40.516368+00:00
-- url     : https://prove2.me/theorems/e817e955-a1bd-47b5-9095-9f47e50acda3
-- title:
--   Theorem 5.2(e) (N) — $U$ is negative
-- statement:
--   Let $\pi$ be a Markov policy of a negative dynamic programming problem and $U$ its operator. For $u\in M(S)$ (so $u\le 0$),
--   $$Uu \le 0 .$$
--
--   This is the negative-case part of Theorem 5.2(e): the paper's (e) says that $U$ is a contraction in the discounted case, positive in the positive bounded case, and negative in the negative case. This item is the negative case only.
--
--   **Formalization Note** $u\in M(S)$ is the hypothesis `IsNegM u`, which includes $u\le0$.
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966), p. 879, Theorem 5.2(e), case N

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_DiscountedDP_Stationary_Operators
import Definitions.Def_NegativeDP_OptEq_Model
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open DiscountedDP.Stationary (Hist Plan MarkovPlan stationary IsGenerated IsGeneratedPlan)

namespace NegativeDP.OptEq

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- Strauch (1966), Theorem 5.2(e), p. 879, negative case: `U` is negative, `u ≤ 0` implies
`Uu ≤ 0` (for `u ∈ M(S)`). -/
theorem theorem52e (P : NegativeDP.Stationary.Problem S A) (π : MarkovPlan S A) (u : S → EReal) (hu : NegativeDP.Stationary.IsNegM u) :
    ∀ s, U P π u s ≤ 0 := by sorry

end NegativeDP.OptEq
