-- Prove2me | Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldGroupPairEntropy_history_pair_entropy_of_sharing
-- name    : OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairEntropy.history_pair_entropy_of_sharing
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:18:46.323964+00:00
-- url     : https://prove2.me/theorems/948be418-4917-4d5b-a6fc-bf89af0a099e
-- title:
--   OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairEntropy.history_pair_entropy_of_sharing: intermediate lemma from OpenAI, Staggered extraction for exact matrix multiplication over every field
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairEntropy.history_pair_entropy_of_sharing` of [lean/OAI/LinearAlgebra/MatrixFields/Entropy/GroupPairEntropy.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Entropy/GroupPairEntropy.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairEntropy`, with `open scoped BigOperators Topology Polynomial`, `open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory AllFieldActiveLaws`, `open AllFieldActiveCapacity AllFieldHistoryChildLaws AllFieldGroupOrbitData`, `open AllFieldGroupDegrees AllFieldGroupNativeLaws AllFieldGroupPairWindows`, `open JointCompatibilityScaling JointCompatibilityRateLimit JointPairClassWindows`, `open scoped BigOperators`):
--
--   ```lean
--   theorem history_pair_entropy_of_sharing (allocation : Allocation) (sigma : Placement)
--       (side : Fin 3) (h : ActiveOrder K tick sigma) (hs : h.val.val.1.stage ≠ 2) :
--       (∑ k : Fin 17, (baseSize (base allocation sigma side) (h, k) : ℝ) *
--         finiteEntropy (q allocation sigma side (h, k))) =
--         (parentBase allocation h : ℝ) *
--           (finiteEntropy (nativePairLaw h.val.val.1 (h.val.val.1.priority side)).mass -
--             finiteEntropy (JointPopulationRates.sideMass (orderLaw h).mass (sigma side)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatrixAllFields.MatrixMultiplication.AllFieldActiveLaws.orderLaw`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.Active`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.ActiveOrder`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.Allocation`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.PlacedWork`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.Placement`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.Work`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.instFintypeStatistic`, `OAI.MatrixAllFields.MatrixMultiplication.FiniteSchedule.lotTick`, `OAI.MatrixAllFields.MatrixMultiplication.Foundation.finiteEntropy`, `OAI.MatrixAllFields.MatrixMultiplication.JointPopulation.Shape`, `OAI.MatrixAllFields.MatrixMultiplication.JointPopulationCompatibility.ClassKey`, `OAI.MatrixAllFields.MatrixMultiplication.JointPopulationRates.sideMass`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.PlacedWork.physicalOrder`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.Work.Statistic`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.Work.lot`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.Work.priority`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.Work.stage` and `OAI.MatrixAllFields.MatrixMultiplication.Foundation.FiniteLaw` (definitions bundle `OAIQ254M000` of this split); `OAI.MatrixAllFields.MatrixMultiplication.JointCompatibilityScaling.baseSize` (definitions bundle `OAIQ254M001` of this split); `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupDegrees.Symbol` (definitions bundle `OAIQ254M003` of this split); `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeLaws.nativePairLaw`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairWindows.base`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairWindows.parentBase` and `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairWindows.q` (definitions bundle `OAIQ254M007` of this split).
--
--   **Used by.** The proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeDegreeBound.nativeCompatibilityRate_eq` of this split imports it.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Entropy/GroupPairEntropy.lean (declaration OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairEntropy.history_pair_entropy_of_sharing)

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

namespace MatrixMultiplication.AllFieldGroupPairEntropy

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory AllFieldActiveLaws
open AllFieldActiveCapacity AllFieldHistoryChildLaws AllFieldGroupOrbitData
open AllFieldGroupDegrees AllFieldGroupNativeLaws AllFieldGroupPairWindows
open JointCompatibilityScaling JointCompatibilityRateLimit JointPairClassWindows
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ} {sigma : Placement}

theorem history_pair_entropy_of_sharing (allocation : Allocation) (sigma : Placement)
    (side : Fin 3) (h : ActiveOrder K tick sigma) (hs : h.val.val.1.stage ≠ 2) :
    (∑ k : Fin 17, (baseSize (base allocation sigma side) (h, k) : ℝ) *
      finiteEntropy (q allocation sigma side (h, k))) =
      (parentBase allocation h : ℝ) *
        (finiteEntropy (nativePairLaw h.val.val.1 (h.val.val.1.priority side)).mass -
          finiteEntropy (JointPopulationRates.sideMass (orderLaw h).mass (sigma side))) := by
  sorry

end MatrixMultiplication.AllFieldGroupPairEntropy

end
end

end MatrixAllFields

end OAI
end
