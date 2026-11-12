-- Prove2me | Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldGroupAmbientDegree_localAllowed_entropy_le
-- name    : OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupAmbientDegree.localAllowed_entropy_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T08:47:55.470564+00:00
-- url     : https://prove2.me/theorems/df2857dc-80e7-4bdf-8d81-ce0658151c80
-- title:
--   OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupAmbientDegree.localAllowed_entropy_le: intermediate lemma from OpenAI, Staggered extraction for exact matrix multiplication over every field
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupAmbientDegree.localAllowed_entropy_le` of [lean/OAI/LinearAlgebra/MatrixFields/Construction/GroupAmbientDegree.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Construction/GroupAmbientDegree.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupAmbientDegree`, with `open scoped BigOperators Topology Polynomial`, `open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory AllFieldActiveLaws`, `open AllFieldActiveCapacity AllFieldGroupTargetRate JointPopulation JointAmbientDegree`, `open JointAmbientEntropy JointGibbsApproximation Filter`, `open scoped BigOperators Topology`):
--
--   ```lean
--   theorem localAllowed_entropy_le (allocation : Allocation) (m : ℕ)
--       (h : ActiveOrder K tick sigma)
--       (word : Positions (orderCounts allocation m) h → JointPopulation.Shape)
--       (hw : localAllowed (orderCounts allocation m) orderTotal h word) :
--       finiteEntropy (fun a => (wordPopulation word a : ℝ) /
--         Fintype.card (Positions (orderCounts allocation m) h)) ≤
--           finiteEntropy (orderLaw h).mass
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.orderCounts`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.orderLaw`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.ActiveOrder`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.Allocation`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.Placement`, `OAI.MatrixAllFields.MatrixMultiplication.Foundation.finiteEntropy`, `OAI.MatrixAllFields.MatrixMultiplication.Foundation.wordPopulation`, `OAI.MatrixAllFields.MatrixMultiplication.JointPopulation.Positions`, `OAI.MatrixAllFields.MatrixMultiplication.JointPopulation.Shape` and `OAI.MatrixAllFields.MatrixMultiplication.Foundation.FiniteLaw` (definitions bundle `OAIQ254M000` of this split); `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupAmbientDegree.orderTotal` and `OAI.MatrixAllFields.MatrixMultiplication.JointAmbientDegree.localAllowed` (definitions bundle `OAIQ254M003` of this split).
--
--   **Used by.** The proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupDegreeLaws.eventually_eligibility_card_le` of this split imports it.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Construction/GroupAmbientDegree.lean (declaration OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupAmbientDegree.localAllowed_entropy_le)

import Mathlib
import Definitions.Def_OAIQ254M003

section

attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldGroupAmbientDegree

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory AllFieldActiveLaws
open AllFieldActiveCapacity AllFieldGroupTargetRate JointPopulation JointAmbientDegree
open JointAmbientEntropy JointGibbsApproximation Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ} {sigma : Placement}

theorem localAllowed_entropy_le (allocation : Allocation) (m : ℕ)
    (h : ActiveOrder K tick sigma)
    (word : Positions (orderCounts allocation m) h → JointPopulation.Shape)
    (hw : localAllowed (orderCounts allocation m) orderTotal h word) :
    finiteEntropy (fun a => (wordPopulation word a : ℝ) /
      Fintype.card (Positions (orderCounts allocation m) h)) ≤
        finiteEntropy (orderLaw h).mass := by
  sorry

end MatrixMultiplication.AllFieldGroupAmbientDegree

end

end MatrixAllFields

end OAI
end
