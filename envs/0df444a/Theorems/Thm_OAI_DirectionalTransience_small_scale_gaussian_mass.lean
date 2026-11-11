-- Prove2me | Theorems.Thm_OAI_DirectionalTransience_small_scale_gaussian_mass
-- name    : OAI.DirectionalTransience.small_scale_gaussian_mass
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:02:20.157948+00:00
-- url     : https://prove2.me/theorems/306365f2-ea3b-4e96-9aae-51497f88fea4
-- title:
--   OAI.DirectionalTransience.small_scale_gaussian_mass: intermediate lemma from OpenAI, Directional transience implies ballisticity
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectionalTransience.directional_transience_implies_ballisticity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Directional transience implies ballisticity*, OpenAI Math Release, September 23, 2026, result family 220, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DirectionalTransience.small_scale_gaussian_mass` of [lean/OAI/Probability/Ballisticity/Estimates/SmallScaleGaussianMass.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Estimates/SmallScaleGaussianMass.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DirectionalTransience`, with `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal Topology`):
--
--   ```lean
--   theorem small_scale_gaussian_mass {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
--       (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
--       (htrans : DirectionallyTransient ν (realPosition (step e))) {ρ : ℝ} (hρ : 0 < ρ) :
--       let ℓ := realPosition (step e)
--       let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
--       let μ := independentConditionedPairLaw ν ℓ
--       let S := commonIncrementProcess ℓ f 0
--       ∃ c : ℝ, 0 < c ∧ ∀ (r : ℕ → ℝ), (∀ n, 0 < r n) → Tendsto r atTop atTop →
--         ∀ (F : ℕ → ℝ) (F₀ : ℝ), 0 < F₀ → (∀ j, F₀ ≤ F j) → Tendsto F atTop (𝓝 F₀) →
--         (∀ j, Tendsto (fun n => truncatedVariance μ S (dyadicCut j*r n)/truncatedVariance μ S (r n)) atTop (𝓝 (F j))) →
--         ∀ b : ℝ, 0 < b → ∀ x : Lattice d, ∀ δ : ℝ, 0 < δ →
--           ∀ᶠ j in atTop, ∀ᶠ n in atTop,
--             (environmentLaw ν).real {ω |
--               (successQuenchedKernel ℓ x (⌊fluctuationScale μ S (dyadicCut j*r n)⌋₊:ℕ) ω).real
--                 (medianTubeEndpoint ν ℓ hp f x ⌊fluctuationScale μ S (dyadicCut j*r n)⌋₊
--                   (b*r n) (ρ*(dyadicCut j*r n))) < c} < δ
--   ```
--
--   **Definitions.** The statement is written with `OAI.DirectionalTransience.NoDrop`, `OAI.DirectionalTransience.commonIncrementProcess`, `OAI.DirectionalTransience.fluctuationScale`, `OAI.DirectionalTransience.independentConditionedPairLaw` and `OAI.DirectionalTransience.truncatedVariance` (definitions bundle `OAIQ242Bal000` of this split); `OAI.DirectionalTransience.dyadicCut` (definitions bundle `OAIQ242Bal001` of this split); `OAI.DirectionalTransience.medianTubeEndpoint` (definitions bundle `OAIQ242Bal003` of this split); `OAI.DirectionalTransience.noDrop_positive_of_directionallyTransient` (definitions bundle `OAIQ242Bal005` of this split); `OAI.DirectionalTransience.successQuenchedKernel` (definitions bundle `OAIQ242Bal006` of this split); `OAI.DirectionalTransience.Direction`, `OAI.DirectionalTransience.DirectionallyTransient`, `OAI.DirectionalTransience.Environment`, `OAI.DirectionalTransience.Lattice`, `OAI.DirectionalTransience.Path`, `OAI.DirectionalTransience.Row`, `OAI.DirectionalTransience.UniformElliptic`, `OAI.DirectionalTransience.Vector`, `OAI.DirectionalTransience.annealedLaw`, `OAI.DirectionalTransience.environmentLaw`, `OAI.DirectionalTransience.realPosition` and `OAI.DirectionalTransience.step` (the published bundle `Def_DirectionalBallisticity`).
--
--   **Used by.** The proof of `OAI.DirectionalTransience.clipping_uniform` of this split imports it.
-- source:
--   OpenAI, Directional transience implies ballisticity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 220; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Estimates/SmallScaleGaussianMass.lean (declaration OAI.DirectionalTransience.small_scale_gaussian_mass)

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal005
import Definitions.Def_OAIQ242Bal006

section

attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

theorem small_scale_gaussian_mass {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) {ρ : ℝ} (hρ : 0 < ρ) :
    let ℓ := realPosition (step e)
    let hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
    let μ := independentConditionedPairLaw ν ℓ
    let S := commonIncrementProcess ℓ f 0
    ∃ c : ℝ, 0 < c ∧ ∀ (r : ℕ → ℝ), (∀ n, 0 < r n) → Tendsto r atTop atTop →
      ∀ (F : ℕ → ℝ) (F₀ : ℝ), 0 < F₀ → (∀ j, F₀ ≤ F j) → Tendsto F atTop (𝓝 F₀) →
      (∀ j, Tendsto (fun n => truncatedVariance μ S (dyadicCut j*r n)/truncatedVariance μ S (r n)) atTop (𝓝 (F j))) →
      ∀ b : ℝ, 0 < b → ∀ x : Lattice d, ∀ δ : ℝ, 0 < δ →
        ∀ᶠ j in atTop, ∀ᶠ n in atTop,
          (environmentLaw ν).real {ω |
            (successQuenchedKernel ℓ x (⌊fluctuationScale μ S (dyadicCut j*r n)⌋₊:ℕ) ω).real
              (medianTubeEndpoint ν ℓ hp f x ⌊fluctuationScale μ S (dyadicCut j*r n)⌋₊
                (b*r n) (ρ*(dyadicCut j*r n))) < c} < δ := by
  sorry

end DirectionalTransience

end

end

end OAI
end
