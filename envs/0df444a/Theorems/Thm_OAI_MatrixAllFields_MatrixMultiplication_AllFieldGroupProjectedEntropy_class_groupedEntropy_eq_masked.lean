-- Prove2me | Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldGroupProjectedEntropy_class_groupedEntropy_eq_masked
-- name    : OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupProjectedEntropy.class_groupedEntropy_eq_masked
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:18:55.077488+00:00
-- url     : https://prove2.me/theorems/d24f6e16-f234-472e-97ee-68da77045077
-- title:
--   OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupProjectedEntropy.class_groupedEntropy_eq_masked (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupProjectedEntropy.class_groupedEntropy_eq_masked` of [lean/OAI/LinearAlgebra/MatrixFields/Entropy/GroupProjectedEntropy.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Entropy/GroupProjectedEntropy.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupProjectedEntropy`, with `open scoped BigOperators Topology Polynomial`, `open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory AllFieldActiveLaws`, `open AllFieldHistoryChildLaws AllFieldGroupOrbitData AllFieldGroupDegrees`, `open AllFieldGroupNativeLaws AllFieldGroupPairWindows AllFieldGroupDegreeLaws`, `open JointCompatibilityScaling JointCompatibilityRateLimit JointCompatibilityControls`, `open JointCompatibilityIncidence JointGroupedEntropyEmbedding`, `open AllFieldGroupBranchDesignation AllFieldNativeGroupedRates`, `open AllFieldScheduledYield AllFieldGroupPairEntropy`, `open scoped BigOperators`):
--
--   ```lean
--   theorem class_groupedEntropy_eq_masked (allocation : Allocation) (right : Bool)
--       (side : Fin 3) (hside : side ≠ 0) (h : ActiveOrder K tick sigma) (k : Fin 17) :
--       groupedEntropy (fun u => (base allocation sigma side (h, k) u : ℝ))
--         (designatedGroup (classDesignated right side sigma (h, k)))
--         (nativeLaw allocation right side sigma (h, k)) =
--         (parentBase allocation h : ℝ) *
--           groupedEntropy (maskedBranchMass h side k)
--             (designatedGroup (nativeBranchDesignated h.val.val.1 right side))
--             (branchHalfLaw h.val.val.1 right side)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.Active`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.ActiveOrder`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.Allocation`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.PlacedWork`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.Placement`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.Work`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.instFintypeBranch`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.instFintypeStatistic`, `OAI.MatrixAllFields.MatrixMultiplication.FiniteSchedule.lotTick`, `OAI.MatrixAllFields.MatrixMultiplication.JointPopulation.Shape`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.PlacedWork.physicalOrder`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.Work.Branch`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.Work.Statistic`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.Work.lot` and `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.Work.stage` (definitions bundle `OAIQ254M000` of this split); `OAI.MatrixAllFields.MatrixMultiplication.JointCompatibilityIncidence.designatedGroup` (definitions bundle `OAIQ254M001` of this split); `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupBranchDesignation.nativeBranchDesignated`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupDegrees.Symbol`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupDegrees.classDesignated` and `OAI.MatrixAllFields.MatrixMultiplication.JointCompatibilityIncidence.groupedEntropy` (definitions bundle `OAIQ254M003` of this split); `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupDegreeLaws.nativeLaw`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairWindows.base`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupPairWindows.parentBase`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupProjectedEntropy.branchHalfLaw` and `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupProjectedEntropy.maskedBranchMass` (definitions bundle `OAIQ254M007` of this split).
--
--   **Used by.** The proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeDegreeBound.nativeCompatibilityRate_eq` of this split imports it.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Entropy/GroupProjectedEntropy.lean (declaration OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupProjectedEntropy.class_groupedEntropy_eq_masked)

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

namespace MatrixMultiplication.AllFieldGroupProjectedEntropy

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory AllFieldActiveLaws
open AllFieldHistoryChildLaws AllFieldGroupOrbitData AllFieldGroupDegrees
open AllFieldGroupNativeLaws AllFieldGroupPairWindows AllFieldGroupDegreeLaws
open JointCompatibilityScaling JointCompatibilityRateLimit JointCompatibilityControls
open JointCompatibilityIncidence JointGroupedEntropyEmbedding
open AllFieldGroupBranchDesignation AllFieldNativeGroupedRates
open AllFieldScheduledYield AllFieldGroupPairEntropy
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ} {sigma : Placement}

theorem class_groupedEntropy_eq_masked (allocation : Allocation) (right : Bool)
    (side : Fin 3) (hside : side ≠ 0) (h : ActiveOrder K tick sigma) (k : Fin 17) :
    groupedEntropy (fun u => (base allocation sigma side (h, k) u : ℝ))
      (designatedGroup (classDesignated right side sigma (h, k)))
      (nativeLaw allocation right side sigma (h, k)) =
      (parentBase allocation h : ℝ) *
        groupedEntropy (maskedBranchMass h side k)
          (designatedGroup (nativeBranchDesignated h.val.val.1 right side))
          (branchHalfLaw h.val.val.1 right side) := by
  sorry

end MatrixMultiplication.AllFieldGroupProjectedEntropy

end
end

end MatrixAllFields

end OAI
end
