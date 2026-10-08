-- Prove2me | Theorems.Thm_MitigateSupplyRisk_LateCommit_corollary_3a
-- name    : MitigateSupplyRisk.LateCommit.corollary_3a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:02:26.870884+00:00
-- url     : https://prove2.me/theorems/045d9a90-afa0-4954-b5a1-4a5ee71a5339
-- title:
--   Corollary 3(a), p. 499 — if Π₁*ᴸ > Π₁*ᴱ at c₁ = ĉ₁ ≤ c₂, then also for every c₁ ∈ [ĉ₁, c₂]
-- statement:
--   Let suppliers 1 and 2 be identical except for their unit costs, with $\hat c_1\le c_2$. Suppose that late commitment strictly outperforms early commitment when supplier 1's unit cost is $c_1=\hat c_1$. Then, with all other data unchanged, it also strictly outperforms early commitment for every $c_1$ with
--   $$\hat c_1\le c_1\le c_2:\qquad \Pi_1^{*L}(c_1)>\Pi_1^{*E}(c_1).$$
--
--   The more similar the suppliers' costs, the less certain the firm is in the first stage which supplier will be preferred, and so the more valuable it is to postpone the selection.
--
--   **Formalization Note** The setting at $c_1=\hat c_1$ is one record $X$, and the setting at $c_1$ is a record $Y$ that agrees with $X$ in everything except supplier 1's unit cost. Part (b) of Corollary 3 is not formalized in this mission.
-- source:
--   Wang, Gilland, Tomlin, Mitigating Supply Risk: Dual Sourcing or Process Improvement?, Manufacturing & Service Operations Management 12(3):489–510 (2010), p. 499 (PDF p. 11), Corollary 3(a)

import Mathlib
import Definitions.Def_MitigateSupplyRisk_LateCommit_Model

namespace MitigateSupplyRisk.LateCommit

/-- Corollary 3(a) (p. 499): in the setting of Theorem 5 (suppliers identical except for unit
costs), if `Π₁^{*L} > Π₁^{*E}` at `c₁ = ĉ₁ ≤ c₂`, then `Π₁^{*L} > Π₁^{*E}` for every
`c₁ ∈ [ĉ₁, c₂]`, all other data unchanged.  Here `X` is the setting at `c₁ = ĉ₁` and `Y`
the setting that differs from `X` only in supplier 1's unit cost. -/
theorem corollary_3a (X : Setting) (hid : X.IdenticalExceptCost) (hc : X.c₁ ≤ X.c₂)
    (hgap : X.earlyValue < X.lateValue)
    (Y : Setting) (hM : Y.M = X.M) (hS₁ : Y.S₁ = X.S₁) (hS₂ : Y.S₂ = X.S₂)
    (hI₁ : Y.I₁ = X.I₁) (hI₂ : Y.I₂ = X.I₂) (hc₂ : Y.c₂ = X.c₂)
    (hlo : X.c₁ ≤ Y.c₁) (hhi : Y.c₁ ≤ Y.c₂) :
    Y.earlyValue < Y.lateValue := by sorry

end MitigateSupplyRisk.LateCommit
