-- Prove2me | Theorems.Thm_OAI_DirectionalTransience_successfulMedian_scaled_tail_comparison
-- name    : OAI.DirectionalTransience.successfulMedian_scaled_tail_comparison
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:02:19.28646+00:00
-- url     : https://prove2.me/theorems/503e7b42-8367-4d13-86b8-676002e66119
-- title:
--   OAI.DirectionalTransience.successfulMedian_scaled_tail_comparison: intermediate lemma from OpenAI, Directional transience implies ballisticity
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectionalTransience.directional_transience_implies_ballisticity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Directional transience implies ballisticity*, OpenAI Math Release, September 23, 2026, result family 220, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DirectionalTransience.successfulMedian_scaled_tail_comparison` of [lean/OAI/Probability/Ballisticity/Estimates/SuccessfulScaledTail.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Estimates/SuccessfulScaledTail.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DirectionalTransience`, with `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal BigOperators Topology`):
--
--   ```lean
--   lemma successfulMedian_scaled_tail_comparison {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
--       (hue : UniformElliptic ν) (e f : Direction d)
--       (htrans : DirectionallyTransient ν (realPosition (step e)))
--       (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
--       (z : ℕ → ℝ) (hz0 : ∀ n, 0 < z n) (hz : Tendsto z atTop atTop)
--       {u : ℝ} (hu : 0 < u) :
--       let ℓ := realPosition (step e)
--       let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
--       let p := (annealedLaw ν (NoDrop ℓ 0)).toReal
--       limsup (fun n => (successfulAverage ν ℓ (H n)).real
--         {X | u < medianDeviation ℓ f (fun j => (recordMedian ν ℓ hp f j:ℝ)) (H n) X / z n}) atTop ≤
--         (20/p^2) * limsup (fun n => (independentConditionedPairLaw ν ℓ).real
--           {P | u/10 < partialSumMax (fun k => commonIncrementProcess ℓ f k P) (H n) / z n}) atTop
--   ```
--
--   **Definitions.** The statement is written with `OAI.DirectionalTransience.NoDrop`, `OAI.DirectionalTransience.commonIncrementProcess` and `OAI.DirectionalTransience.independentConditionedPairLaw` (definitions bundle `OAIQ242Bal000` of this split); `OAI.DirectionalTransience.partialSumMax` (definitions bundle `OAIQ242Bal001` of this split); `OAI.DirectionalTransience.medianDeviation`, `OAI.DirectionalTransience.recordMedian` and `OAI.DirectionalTransience.successfulAverage` (definitions bundle `OAIQ242Bal003` of this split); `OAI.DirectionalTransience.noDrop_positive_of_directionallyTransient` (definitions bundle `OAIQ242Bal005` of this split); `OAI.DirectionalTransience.Direction`, `OAI.DirectionalTransience.DirectionallyTransient`, `OAI.DirectionalTransience.Lattice`, `OAI.DirectionalTransience.Path`, `OAI.DirectionalTransience.Row`, `OAI.DirectionalTransience.UniformElliptic`, `OAI.DirectionalTransience.Vector`, `OAI.DirectionalTransience.annealedLaw`, `OAI.DirectionalTransience.realPosition` and `OAI.DirectionalTransience.step` (the published bundle `Def_DirectionalBallisticity`).
--
--   **Used by.** The proofs of `OAI.DirectionalTransience.successful_small_variance_bound` and `OAI.DirectionalTransience.successful_tail_profile_bound` of this split import it.
-- source:
--   OpenAI, Directional transience implies ballisticity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 220; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Estimates/SuccessfulScaledTail.lean (declaration OAI.DirectionalTransience.successfulMedian_scaled_tail_comparison)

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal005

section

attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma successfulMedian_scaled_tail_comparison {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (H : ℕ → ℕ) (hH : Tendsto H atTop atTop)
    (z : ℕ → ℝ) (hz0 : ∀ n, 0 < z n) (hz : Tendsto z atTop atTop)
    {u : ℝ} (hu : 0 < u) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let p := (annealedLaw ν (NoDrop ℓ 0)).toReal
    limsup (fun n => (successfulAverage ν ℓ (H n)).real
      {X | u < medianDeviation ℓ f (fun j => (recordMedian ν ℓ hp f j:ℝ)) (H n) X / z n}) atTop ≤
      (20/p^2) * limsup (fun n => (independentConditionedPairLaw ν ℓ).real
        {P | u/10 < partialSumMax (fun k => commonIncrementProcess ℓ f k P) (H n) / z n}) atTop := by
  sorry

end DirectionalTransience

end

end

end OAI
end
