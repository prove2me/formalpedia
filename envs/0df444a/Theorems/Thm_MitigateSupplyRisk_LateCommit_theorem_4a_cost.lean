-- Prove2me | Theorems.Thm_MitigateSupplyRisk_LateCommit_theorem_4a_cost
-- name    : MitigateSupplyRisk.LateCommit.theorem_4a_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:02:26.813248+00:00
-- url     : https://prove2.me/theorems/0a8d6a88-f58f-45cc-a569-58174a8c8582
-- title:
--   Theorem 4(a), p. 497, cost-only instance — suppliers differing only in unit cost: i* = j* (the cheaper one)
-- statement:
--   Let suppliers 1 and 2 be identical except for their unit costs, with $c_1\le c_2$. Let $j^*$ be the firm's preferred supplier if reliability improvement is not possible, and $i^*$ the preferred supplier under early commitment if improvement is possible. Then supplier 1 is (weakly) preferred in both cases:
--   $$\Pi_2^*(a_2^0)\le\Pi_2^*(a_1^0)\qquad\text{and}\qquad\sup_{a\ge a_2^0}\Pi_{12}^E(a)\le\sup_{a\ge a_1^0}\Pi_{11}^E(a),$$
--   where the left-hand $\Pi_2^*$ is supplier 2's single-sourcing value and the right-hand one is supplier 1's. Hence $i^*=j^*=1$.
--
--   This is the instance of Theorem 4(a), "if suppliers 1 and 2 differ in at most one attribute, then $i^*=j^*$", in which the attribute is the unit cost. It also shows that under the hypotheses of Theorem 5 the early-commitment optimum is attained by supplier 1.
--
--   **Formalization Note** "Identical except for unit costs" means that the two suppliers share the loss family, capacity, committed cost, initial index, success probability, improvement cost and effort function. The preference is read weakly, so ties are allowed and $i^*=j^*=1$ is one consistent choice of preferred suppliers. Theorem 4(a) for other single attributes and Theorem 4(b) are not formalized.
-- source:
--   Wang, Gilland, Tomlin, Mitigating Supply Risk: Dual Sourcing or Process Improvement?, Manufacturing & Service Operations Management 12(3):489–510 (2010), p. 497 (PDF p. 9), Theorem 4(a), cost-only instance

import Mathlib
import Definitions.Def_MitigateSupplyRisk_LateCommit_Model

namespace MitigateSupplyRisk.LateCommit

/-- Theorem 4(a), cost-only instance (p. 497): if the suppliers are identical except for their
unit costs and `c₁ ≤ c₂`, then supplier 1 is (weakly) preferred both when improvement is not
possible (`Π₂*(a₁⁰) ≥ Π₂*(a₂⁰)`, so `j* = 1`) and when it is (early-commitment optimal value of
supplier 1 ≥ that of supplier 2, so `i* = 1`); hence `i* = j*`. -/
theorem theorem_4a_cost (X : Setting) (hid : X.IdenticalExceptCost) (hc : X.c₁ ≤ X.c₂) :
    X.P₂ X.I₂.a0 ≤ X.P₁ X.I₁.a0 ∧ X.earlyValue₂ ≤ X.earlyValue₁ := by sorry

end MitigateSupplyRisk.LateCommit
