-- Prove2me | Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldGroupCountRate_exists_widths_eventually_nativeCount_le
-- name    : OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupCountRate.exists_widths_eventually_nativeCount_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:18:31.122831+00:00
-- url     : https://prove2.me/theorems/9a3dea59-2e98-4713-b020-3c2542cf14de
-- title:
--   OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupCountRate.exists_widths_eventually_nativeCount_le (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupCountRate.exists_widths_eventually_nativeCount_le` of [lean/OAI/LinearAlgebra/MatrixFields/Entropy/GroupCountRate.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Entropy/GroupCountRate.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupCountRate`, with `open scoped BigOperators Topology Polynomial`, `open AllFieldHistory AllFieldHistorySupport AllFieldHistoryChildLaws`, `open AllFieldGroupOrbitData AllFieldGroupDegrees AllFieldGroupDegreeLaws`, `open AllFieldGroupNativeLaws AllFieldGroupPairWindows`, `open JointCompatibilityControls JointCompatibilityScaling JointCompatibilityRateLimit`, `open JointPopulationCompatibility JointTypeCounts MatrixMultiplication.Foundation Filter`, `open scoped BigOperators Topology`):
--
--   ```lean
--   theorem exists_widths_eventually_nativeCount_le (allocation : Allocation) (sigma : Placement)
--       (side : Fin 3) {δ χMax ηMax : ℝ}
--       (hδ : 0 < δ) (hχMax : 0 < χMax) (hηMax : 0 < ηMax) :
--       ∃ χ η : ℝ, 0 < χ ∧ χ ≤ χMax ∧ 0 < η ∧ η ≤ ηMax ∧
--         ∀ᶠ m : ℕ in atTop,
--           ∀ (e : Targets (K := K) (tick := tick) allocation m sigma)
--             (w : Raw (K := K) (tick := tick) allocation m sigma),
--             (∀ h j, JointPopulation.shapeSide (sigma side) ((e h).val j) =
--               ownWord allocation m sigma w ⟨h, j⟩) →
--             PairWindow (base allocation sigma side) (q allocation sigma side)
--               (Positions (K := K) (tick := tick) allocation m sigma w) (pairCounts allocation m sigma w) η →
--             (nativeCount allocation m χ sigma side w : ℝ) ≤
--               Real.exp ((m : ℝ) *
--                 (nativeCompatibilityRate (K := K) (tick := tick) allocation sigma side + δ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.Counts`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.Raw`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.Targets`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.ownWord`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.ActiveOrder`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.Allocation`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.Placement`, `OAI.MatrixAllFields.MatrixMultiplication.Foundation.wordPopulation`, `OAI.MatrixAllFields.MatrixMultiplication.JointPopulation.Positions`, `OAI.MatrixAllFields.MatrixMultiplication.JointPopulation.Shape`, `OAI.MatrixAllFields.MatrixMultiplication.JointPopulation.shapeSide` and `OAI.MatrixAllFields.MatrixMultiplication.JointPopulationCompatibility.ClassKey` (definitions bundle `OAIQ254M000` of this split); `OAI.MatrixAllFields.MatrixMultiplication.JointCompatibilityRateLimit.PairWindow` (definitions bundle `OAIQ254M001` of this split); `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupDegrees.Symbol` (definitions bundle `OAIQ254M003` of this split); `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupCountRate.nativeCompatibilityRate`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupDegreeLaws.nativeCount`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairWindows.Positions`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairWindows.base`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairWindows.pairCounts` and `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairWindows.q` (definitions bundle `OAIQ254M007` of this split).
--
--   **Used by.** The proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeDegreeBound.exists_threshold_eventually_counts_le` of this split imports it.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Entropy/GroupCountRate.lean (declaration OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupCountRate.exists_widths_eventually_nativeCount_le)

import Mathlib
import Definitions.Def_OAIQ254M007

section

attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryIteration.labelsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldTerminalRates.zeroWordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.designatedDecidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupCountRate

open AllFieldHistory AllFieldHistorySupport AllFieldHistoryChildLaws
open AllFieldGroupOrbitData AllFieldGroupDegrees AllFieldGroupDegreeLaws
open AllFieldGroupNativeLaws AllFieldGroupPairWindows
open JointCompatibilityControls JointCompatibilityScaling JointCompatibilityRateLimit
open JointPopulationCompatibility JointTypeCounts MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

theorem exists_widths_eventually_nativeCount_le (allocation : Allocation) (sigma : Placement)
    (side : Fin 3) {δ χMax ηMax : ℝ}
    (hδ : 0 < δ) (hχMax : 0 < χMax) (hηMax : 0 < ηMax) :
    ∃ χ η : ℝ, 0 < χ ∧ χ ≤ χMax ∧ 0 < η ∧ η ≤ ηMax ∧
      ∀ᶠ m : ℕ in atTop,
        ∀ (e : Targets (K := K) (tick := tick) allocation m sigma)
          (w : Raw (K := K) (tick := tick) allocation m sigma),
          (∀ h j, JointPopulation.shapeSide (sigma side) ((e h).val j) =
            ownWord allocation m sigma w ⟨h, j⟩) →
          PairWindow (base allocation sigma side) (q allocation sigma side)
            (Positions (K := K) (tick := tick) allocation m sigma w) (pairCounts allocation m sigma w) η →
          (nativeCount allocation m χ sigma side w : ℝ) ≤
            Real.exp ((m : ℝ) *
              (nativeCompatibilityRate (K := K) (tick := tick) allocation sigma side + δ)) := by
  sorry

end MatrixMultiplication.AllFieldGroupCountRate

end
end

end MatrixAllFields

end OAI
end
