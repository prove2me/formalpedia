-- Prove2me | Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldGroupSelection_exists_threshold_eventually_selected
-- name    : OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupSelection.exists_threshold_eventually_selected
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:18:36.149232+00:00
-- url     : https://prove2.me/theorems/dd9de754-c52a-4c35-9b5a-22d845e3c55c
-- title:
--   OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupSelection.exists_threshold_eventually_selected (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupSelection.exists_threshold_eventually_selected` of [lean/OAI/LinearAlgebra/MatrixFields/Extraction/GroupSelection.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Extraction/GroupSelection.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupSelection`, with `open scoped BigOperators Topology Polynomial`, `open MatrixMultiplication.Foundation AllFieldHistory AllFieldActiveLaws`, `open AllFieldActiveCapacity AllFieldScheduledYield AllFieldNativeCapacity`, `open Filter`, `open scoped BigOperators Topology`):
--
--   ```lean
--   theorem exists_threshold_eventually_selected
--       (allocation : Allocation) (sigma : Placement)
--       {slack widthMax : ℝ} (hslack : 0 < slack) (hwidthMax : 0 < widthMax) :
--       ∃ threshold : ℝ, 0 < threshold ∧ threshold ≤ widthMax ∧
--         ∀ width : ℝ, 0 < width → width ≤ threshold →
--           ∀ᶠ m : ℕ in atTop,
--             Nonempty (Selected (K := K) (tick := tick) allocation m width sigma slack)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.Allocation` and `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.Placement` (definitions bundle `OAIQ254M000` of this split); `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupSelection.Selected` (definitions bundle `OAIQ254M002` of this split).
--
--   **Used by.** The proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionFamily.fixed_allocation_constraint` of this split imports it.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Extraction/GroupSelection.lean (declaration OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupSelection.exists_threshold_eventually_selected)

import Mathlib
import Definitions.Def_OAIQ254M002

section

attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupSelection

open MatrixMultiplication.Foundation AllFieldHistory AllFieldActiveLaws
open AllFieldActiveCapacity AllFieldScheduledYield AllFieldNativeCapacity
open Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

variable {K tick : ℕ}

theorem exists_threshold_eventually_selected
    (allocation : Allocation) (sigma : Placement)
    {slack widthMax : ℝ} (hslack : 0 < slack) (hwidthMax : 0 < widthMax) :
    ∃ threshold : ℝ, 0 < threshold ∧ threshold ≤ widthMax ∧
      ∀ width : ℝ, 0 < width → width ≤ threshold →
        ∀ᶠ m : ℕ in atTop,
          Nonempty (Selected (K := K) (tick := tick) allocation m width sigma slack) := by
  sorry

end MatrixMultiplication.AllFieldGroupSelection

end
end

end MatrixAllFields

end OAI
end
