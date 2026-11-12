-- Prove2me | Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldActiveCapacity_workCapacity_stageC_physical
-- name    : OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveCapacity.workCapacity_stageC_physical
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T07:11:40.213053+00:00
-- url     : https://prove2.me/theorems/d4ad49c1-79a7-4cde-874b-31b3fa04e033
-- title:
--   OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveCapacity.workCapacity_stageC_physical: intermediate lemma from OpenAI, Staggered extraction for exact matrix multiplication over every field
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveCapacity.workCapacity_stageC_physical` of [lean/OAI/LinearAlgebra/MatrixFields/Parameters/GroupSelectionParameters.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Parameters/GroupSelectionParameters.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveCapacity`, with `open scoped BigOperators Topology Polynomial`, `open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory`, `open AllFieldNativeCapacity AllFieldActiveLaws AllFieldScheduledYield`, `open scoped BigOperators`):
--
--   ```lean
--   theorem workCapacity_stageC_physical {K : ℕ} (h : PartC K)
--       (phi : Placement) (i : Fin 3) :
--       workCapacity (.stageC h) i = finiteEntropy
--         (JointPopulationRates.sideMass (placedLaw (.stageC h, phi)).mass
--           ((PlacedWork.physicalOrder (.stageC h, phi)) i))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.placedLaw`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.PartC`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.Placement`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.Work`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldScheduledYield.workCapacity`, `OAI.MatrixAllFields.MatrixMultiplication.Foundation.finiteEntropy`, `OAI.MatrixAllFields.MatrixMultiplication.JointPopulation.Shape`, `OAI.MatrixAllFields.MatrixMultiplication.JointPopulationRates.sideMass`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.PlacedWork.physicalOrder` and `OAI.MatrixAllFields.MatrixMultiplication.Foundation.FiniteLaw` (definitions bundle `OAIQ254M000` of this split).
--
--   **Used by.** The proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupProjectedEntropy.branchConditionalCost_eq_observed` of this split imports it.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Parameters/GroupSelectionParameters.lean (declaration OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveCapacity.workCapacity_stageC_physical)

import Mathlib
import Definitions.Def_OAIQ254M000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.AllFieldActiveCapacity

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open AllFieldNativeCapacity AllFieldActiveLaws AllFieldScheduledYield
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

theorem workCapacity_stageC_physical {K : ℕ} (h : PartC K)
    (phi : Placement) (i : Fin 3) :
    workCapacity (.stageC h) i = finiteEntropy
      (JointPopulationRates.sideMass (placedLaw (.stageC h, phi)).mass
        ((PlacedWork.physicalOrder (.stageC h, phi)) i)) := by
  sorry

end MatrixMultiplication.AllFieldActiveCapacity

end

end MatrixAllFields

end OAI
end
