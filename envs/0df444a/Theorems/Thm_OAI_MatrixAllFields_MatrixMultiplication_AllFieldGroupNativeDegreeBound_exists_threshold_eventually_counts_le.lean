-- Prove2me | Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldGroupNativeDegreeBound_exists_threshold_eventually_counts_le
-- name    : OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeDegreeBound.exists_threshold_eventually_counts_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T06:44:12.943001+00:00
-- url     : https://prove2.me/theorems/18fc1de0-6ead-4921-a32b-375bf5937702
-- title:
--   OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeDegreeBound.exists_threshold_eventually_counts_le (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldMain.omega_lt_source_constant`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Staggered extraction for exact matrix multiplication over every field*, OpenAI Math Release, September 24, 2026, result family 107, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeDegreeBound.exists_threshold_eventually_counts_le` of [lean/OAI/LinearAlgebra/MatrixFields/Construction/GroupNativeDegreeBound.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Construction/GroupNativeDegreeBound.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeDegreeBound`, with `open scoped BigOperators Topology Polynomial`, `open AllFieldHistory AllFieldActiveLaws AllFieldActiveCapacity`, `open AllFieldGroupOrbitData AllFieldGroupDegrees AllFieldGroupDegreeLaws`, `open AllFieldGroupCountRate AllFieldGroupPairWindows AllFieldGroupPairEntropy`, `open AllFieldGroupProjectedEntropy JointCompatibilityRateLimit`, `open MatrixMultiplication.Foundation Filter`, `open scoped BigOperators Topology`):
--
--   ```lean
--   theorem exists_threshold_eventually_counts_le (allocation : Allocation) (sigma : Placement)
--       {δ widthMax : ℝ} (hδ : 0 < δ) (hwidthMax : 0 < widthMax) :
--       ∃ threshold : ℝ, 0 < threshold ∧ threshold ≤ widthMax ∧
--         ∀ width : ℝ, 0 < width → width ≤ threshold →
--           ∀ᶠ m : ℕ in atTop,
--             (∀ e : Targets (K := K) (tick := tick) allocation m sigma,
--               (((data allocation m width sigma).eligibilityCompetitors e).card : ℝ) ≤
--                 Real.exp ((m : ℝ) * (maxNativeDegree (K := K) (tick := tick) allocation sigma + δ))) ∧
--             (∀ (e : Targets (K := K) (tick := tick) allocation m sigma) (o : Orbit (K := K) (tick := tick) allocation m sigma),
--               o ∈ (data allocation m width sigma).orbits e →
--               ∀ v : Variable (K := K) (tick := tick) allocation m sigma,
--                 v ∈ (data allocation m width sigma).passing e o →
--                 (((data allocation m width sigma).competitors e o v).card : ℝ) ≤
--                   Real.exp ((m : ℝ) * (maxNativeDegree (K := K) (tick := tick) allocation sigma + δ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.Orbit`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.Pos`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.Targets`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.Variable`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.Allocation`, `OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistory.Placement`, `OAI.MatrixAllFields.MatrixMultiplication.JointCoarseHashing.Triple`, `OAI.MatrixAllFields.MatrixMultiplication.JointMaskedSelection.OrbitData` and `OAI.MatrixAllFields.MatrixMultiplication.JointMaskedSelection.OrbitData.eligibilityCompetitors` (definitions bundle `OAIQ254M000` of this split); `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupOrbitData.data` (definitions bundle `OAIQ254M002` of this split); `OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeDegreeBound.maxNativeDegree` (definitions bundle `OAIQ254M007` of this split).
--
--   **Used by.** The proof of `OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionFamily.fixed_allocation_constraint` of this split imports it.
-- source:
--   OpenAI, Staggered extraction for exact matrix multiplication over every field, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 107; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026/Staggered-extraction-for-exact-matrix-multiplication-over-every-field-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/LinearAlgebra/MatrixFields/Construction/GroupNativeDegreeBound.lean (declaration OAI.MatrixAllFields.MatrixMultiplication.AllFieldGroupNativeDegreeBound.exists_threshold_eventually_counts_le)

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

namespace MatrixMultiplication.AllFieldGroupNativeDegreeBound

open AllFieldHistory AllFieldActiveLaws AllFieldActiveCapacity
open AllFieldGroupOrbitData AllFieldGroupDegrees AllFieldGroupDegreeLaws
open AllFieldGroupCountRate AllFieldGroupPairWindows AllFieldGroupPairEntropy
open AllFieldGroupProjectedEntropy JointCompatibilityRateLimit
open MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

theorem exists_threshold_eventually_counts_le (allocation : Allocation) (sigma : Placement)
    {δ widthMax : ℝ} (hδ : 0 < δ) (hwidthMax : 0 < widthMax) :
    ∃ threshold : ℝ, 0 < threshold ∧ threshold ≤ widthMax ∧
      ∀ width : ℝ, 0 < width → width ≤ threshold →
        ∀ᶠ m : ℕ in atTop,
          (∀ e : Targets (K := K) (tick := tick) allocation m sigma,
            (((data allocation m width sigma).eligibilityCompetitors e).card : ℝ) ≤
              Real.exp ((m : ℝ) * (maxNativeDegree (K := K) (tick := tick) allocation sigma + δ))) ∧
          (∀ (e : Targets (K := K) (tick := tick) allocation m sigma) (o : Orbit (K := K) (tick := tick) allocation m sigma),
            o ∈ (data allocation m width sigma).orbits e →
            ∀ v : Variable (K := K) (tick := tick) allocation m sigma,
              v ∈ (data allocation m width sigma).passing e o →
              (((data allocation m width sigma).competitors e o v).card : ℝ) ≤
                Real.exp ((m : ℝ) * (maxNativeDegree (K := K) (tick := tick) allocation sigma + δ))) := by
  sorry

end MatrixMultiplication.AllFieldGroupNativeDegreeBound

end
end

end MatrixAllFields

end OAI
end
