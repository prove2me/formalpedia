-- Prove2me | Theorems.Thm_OAI_DirectionalTransience_shared_limit_finite_past_identity
-- name    : OAI.DirectionalTransience.shared_limit_finite_past_identity
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:00:14.824703+00:00
-- url     : https://prove2.me/theorems/678c1467-79b3-43ea-8d8d-850dbc315d62
-- title:
--   OAI.DirectionalTransience.shared_limit_finite_past_identity: intermediate lemma from OpenAI, Directional transience implies ballisticity
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectionalTransience.directional_transience_implies_ballisticity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Directional transience implies ballisticity*, OpenAI Math Release, September 23, 2026, result family 220, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DirectionalTransience.shared_limit_finite_past_identity` of [lean/OAI/Probability/Ballisticity/Estimates/SharedLimitPastIdentity.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Estimates/SharedLimitPastIdentity.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DirectionalTransience`, with `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction`):
--
--   ```lean
--   theorem shared_limit_finite_past_identity {d q : ℕ} (ν : Measure (Row d))
--       [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
--       (htrans : DirectionallyTransient ν (realPosition (step e)))
--       (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
--         (commonIncrementProcess (realPosition (step e)) f 0) r)
--       (hn : ∀ i, 0 < fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
--         (commonIncrementProcess (realPosition (step e)) f 0) (r i))
--       (T : ℝ) (hT : 0 < T) (k : ℕ → ℕ)
--       (hk : ∀ i, (k i:ℝ) ≤ T*fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
--         (commonIncrementProcess (realPosition (step e)) f 0) (r i))
--       (t : ℝ) (hkt : Tendsto (fun i => (k i:ℝ)/fluctuationScale
--         (independentConditionedPairLaw ν (realPosition (step e)))
--         (commonIncrementProcess (realPosition (step e)) f 0) (r i)) atTop (𝓝 t))
--       (x y : ℕ → Lattice d) (hxy : ∀ i, signedHeight e (x i) = signedHeight e (y i))
--       (H : ℕ → ℕ) (hH : ∀ i, 0 < H i) (j : ℕ → Fin q → ℕ) (hj : ∀ i z, j i z ≤ H i)
--       (a : ℕ → JointPastTimes q) (a₀ : JointPastTimes q) (ha : Tendsto a atTop (𝓝 a₀))
--       (μ : ℕ → ProbabilityMeasure RealPathPair) (V : ProbabilityMeasure RealPathPair)
--       (hweak : Tendsto μ atTop (𝓝 V))
--       (F : (Fin q → ℝ × ℝ) →ᵇ ℝ) (G : ℝ →ᵇ ℝ) (hG : UniformContinuous G) (b : Bool) :
--       let ℓ := realPosition (step e)
--       let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
--       let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
--       let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
--       (∀ i z, T*n i*(a i |>.1 z : ℝ) = j i z) →
--       (∀ i, T*n i*(a i |>.2.1 : ℝ) = H i) →
--       (∀ i, T*n i*(a i |>.2.2 : ℝ) = H i+k i) →
--       (∀ i, (μ i : Measure RealPathPair) = (sharedConditionedPairLaw ν ℓ (x i) (y i)).map
--         (sharedLinearPairPath ℓ f (θ i) (r i) (n i) T (x i) (y i))) →
--       (∫ P, jointPastProductTest F G (∫ z, G z ∂gaussianReal 0 (Real.toNNReal (t/(2*commonMeanWidth ν ℓ))))
--         (jointPastIncrementMap b (P,a₀)) ∂(V : Measure RealPathPair)) = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.DirectionalTransience.NoDrop`, `OAI.DirectionalTransience.commonIncrementProcess`, `OAI.DirectionalTransience.fluctuationScale`, `OAI.DirectionalTransience.independentConditionedPairLaw` and `OAI.DirectionalTransience.signedHeight` (definitions bundle `OAIQ242Bal000` of this split); `OAI.DirectionalTransience.JointPastTimes`, `OAI.DirectionalTransience.RealPathPair`, `OAI.DirectionalTransience.continuousPathBorelSpace`, `OAI.DirectionalTransience.continuousPathMeasurableSpace`, `OAI.DirectionalTransience.jointPastIncrementMap` and `OAI.DirectionalTransience.jointPastProductTest` (definitions bundle `OAIQ242Bal001` of this split); `OAI.DirectionalTransience.IsGaussianSequence`, `OAI.DirectionalTransience.commonMeanWidth` and `OAI.DirectionalTransience.sharedConditionedPairLaw` (definitions bundle `OAIQ242Bal002` of this split); `OAI.DirectionalTransience.recordMedianSlope` and `OAI.DirectionalTransience.sharedLinearPairPath` (definitions bundle `OAIQ242Bal003` of this split); `OAI.DirectionalTransience.noDrop_positive_of_directionallyTransient` (definitions bundle `OAIQ242Bal005` of this split); `OAI.DirectionalTransience.Direction`, `OAI.DirectionalTransience.DirectionallyTransient`, `OAI.DirectionalTransience.Lattice`, `OAI.DirectionalTransience.Path`, `OAI.DirectionalTransience.Row`, `OAI.DirectionalTransience.UniformElliptic`, `OAI.DirectionalTransience.Vector`, `OAI.DirectionalTransience.annealedLaw`, `OAI.DirectionalTransience.realPosition` and `OAI.DirectionalTransience.step` (the published bundle `Def_DirectionalBallisticity`).
--
--   **Used by.** The proof of `OAI.DirectionalTransience.shared_pair_path_limit` of this split imports it.
-- source:
--   OpenAI, Directional transience implies ballisticity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 220; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Estimates/SharedLimitPastIdentity.lean (declaration OAI.DirectionalTransience.shared_limit_finite_past_identity)

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal005

section

attribute [-instance] _root_.OAI.DirectionalTransience.ReferenceClasses.data_compact _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology BoundedContinuousFunction
namespace DirectionalTransience

theorem shared_limit_finite_past_identity {d q : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    (hn : ∀ i, 0 < fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) (r i))
    (T : ℝ) (hT : 0 < T) (k : ℕ → ℕ)
    (hk : ∀ i, (k i:ℝ) ≤ T*fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) (r i))
    (t : ℝ) (hkt : Tendsto (fun i => (k i:ℝ)/fluctuationScale
      (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) (r i)) atTop (𝓝 t))
    (x y : ℕ → Lattice d) (hxy : ∀ i, signedHeight e (x i) = signedHeight e (y i))
    (H : ℕ → ℕ) (hH : ∀ i, 0 < H i) (j : ℕ → Fin q → ℕ) (hj : ∀ i z, j i z ≤ H i)
    (a : ℕ → JointPastTimes q) (a₀ : JointPastTimes q) (ha : Tendsto a atTop (𝓝 a₀))
    (μ : ℕ → ProbabilityMeasure RealPathPair) (V : ProbabilityMeasure RealPathPair)
    (hweak : Tendsto μ atTop (𝓝 V))
    (F : (Fin q → ℝ × ℝ) →ᵇ ℝ) (G : ℝ →ᵇ ℝ) (hG : UniformContinuous G) (b : Bool) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let n := fun i => fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0) (r i)
    let θ := fun i => recordMedianSlope ν ℓ hp f (r i)
    (∀ i z, T*n i*(a i |>.1 z : ℝ) = j i z) →
    (∀ i, T*n i*(a i |>.2.1 : ℝ) = H i) →
    (∀ i, T*n i*(a i |>.2.2 : ℝ) = H i+k i) →
    (∀ i, (μ i : Measure RealPathPair) = (sharedConditionedPairLaw ν ℓ (x i) (y i)).map
      (sharedLinearPairPath ℓ f (θ i) (r i) (n i) T (x i) (y i))) →
    (∫ P, jointPastProductTest F G (∫ z, G z ∂gaussianReal 0 (Real.toNNReal (t/(2*commonMeanWidth ν ℓ))))
      (jointPastIncrementMap b (P,a₀)) ∂(V : Measure RealPathPair)) = 0 := by
  sorry

end DirectionalTransience

end

end

end OAI
end
