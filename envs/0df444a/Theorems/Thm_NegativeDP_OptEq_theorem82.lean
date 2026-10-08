-- Prove2me | Theorems.Thm_NegativeDP_OptEq_theorem82
-- name    : NegativeDP.OptEq.theorem82
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:53:50.335212+00:00
-- url     : https://prove2.me/theorems/52bb339f-4051-43e5-942a-c234dfc5bdbc
-- title:
--   Theorem 8.2 (N) — the optimal return satisfies the optimality equation $v^* = \sup_a T_a v^*$
-- statement:
--   Consider a negative dynamic programming problem: non-empty Borel state and action sets $S$ and $A$, a law of motion $q(\cdot\mid s,a)$, and a Borel return $r(s,a,t)$ with $-\infty < r \le 0$ and finite expected one-step return. Let
--   $$v^*(s) = \sup_\pi I(\pi)(s)$$
--   be the optimal return, the supremum of the expected total return over all policies (randomized and history-dependent), and for an action $a$ let
--   $$T_a u(s) = \int \big[r(s,a,t) + u(t)\big]\,dq(t\mid s,a).$$
--   Then $v^*$ satisfies the **optimality equation**
--   $$v^*(s) = \sup_{a\in A} T_a v^*(s) \qquad\text{for all } s\in S.$$
--
--   The equation holds although $v^*$ need not be Borel measurable; the integral is meaningful because $v^*$ is absolutely measurable (Theorem 7.1). It is the starting point for every characterization of optimal policies in the negative case, for instance that a stationary policy is optimal if and only if it attains the supremum and its own return equals $v^*$.
--
--   The paper states Theorem 8.2 for the discounted, positive and negative cases, and adds that in the discounted case $v^*$ is the unique bounded solution and in the positive bounded case the smallest non-negative solution. That sentence concerns the discounted and positive cases only and is not part of this item, which is the negative case.
--
--   **Formalization Note** $v^*$ is not assumed measurable. $T_a v^*$ is computed as minus the lower Lebesgue integral (`lintegral`) of the loss $-r - v^* \ge 0$. `lintegral` is defined for every function and does not change when the integrand is modified on a null set, so for the absolutely measurable $v^*$ it equals the completion integral the paper means. The supremum is over all of $A$. Values are in `EReal`; $v^*\le0$ holds because every return is $\le0$.
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966), p. 885, Theorem 8.2 (T_a defined on p. 885, v* on p. 883)

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

/-- Strauch (1966), Theorem 8.2, p. 885, negative case: the optimal return satisfies the
optimality equation `v*(s) = sup_a T_a v*(s)` for all `s ∈ S`. `v*` is not assumed measurable;
`T_a v*` is a lower Lebesgue integral of the loss. -/
theorem theorem82 (P : NegativeDP.Stationary.Problem S A) :
    ∀ s, NegativeDP.Stationary.vstar P s = ⨆ a : A, Ta P a (NegativeDP.Stationary.vstar P) s := by sorry

end NegativeDP.OptEq
