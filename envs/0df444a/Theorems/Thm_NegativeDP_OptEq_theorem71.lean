-- Prove2me | Theorems.Thm_NegativeDP_OptEq_theorem71
-- name    : NegativeDP.OptEq.theorem71
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:53:51.541251+00:00
-- url     : https://prove2.me/theorems/fed75ac4-075c-44b6-ac99-2155cde821b3
-- title:
--   Theorem 7.1 (N) — the optimal return $v^*$ is absolutely measurable
-- statement:
--   In a negative dynamic programming problem, let $v^*(s) = \sup_\pi I(\pi)(s)$ be the optimal return, the supremum over all policies. Then $v^*$ is **absolutely measurable**: for every probability measure $p$ on $S$, $v^*$ is measurable with respect to the completion of the Borel σ-field under $p$.
--
--   In general $v^*$ is not Borel measurable (the paper's Examples 4.1 and 6.2). Absolute measurability is what gives the integrals $\int v^*(t)\,dq(t\mid s,a)$ in the optimality equation, and the notion of $(p,\varepsilon)$-optimality, their meaning.
--
--   The paper states this for the discounted, positive and negative cases; this item is the negative case. **Formalization Note** "Measurable with respect to the completion of $p$" is Mathlib's `NullMeasurable (vstar P) p`, required for every probability measure $p$ on $S$. $v^*$ takes values in $[-\infty,0]$ (`EReal`).
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966), p. 884, Theorem 7.1 (absolute measurability defined on p. 883)

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

/-- Strauch (1966), Theorem 7.1, p. 884, negative case: `v*` is absolutely measurable, i.e.
measurable with respect to the completion of every probability measure `p` on `S`. -/
theorem theorem71 (P : NegativeDP.Stationary.Problem S A) :
    ∀ p : Measure S, IsProbabilityMeasure p → NullMeasurable (NegativeDP.Stationary.vstar P) p := by sorry

end NegativeDP.OptEq
