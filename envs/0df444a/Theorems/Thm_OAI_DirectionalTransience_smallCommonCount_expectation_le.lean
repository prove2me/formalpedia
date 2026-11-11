-- Prove2me | Theorems.Thm_OAI_DirectionalTransience_smallCommonCount_expectation_le
-- name    : OAI.DirectionalTransience.smallCommonCount_expectation_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:01:41.676492+00:00
-- url     : https://prove2.me/theorems/5732768f-efac-4603-81c9-845e36988a26
-- title:
--   OAI.DirectionalTransience.smallCommonCount_expectation_le: intermediate lemma from OpenAI, Directional transience implies ballisticity
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectionalTransience.directional_transience_implies_ballisticity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Directional transience implies ballisticity*, OpenAI Math Release, September 23, 2026, result family 220, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DirectionalTransience.smallCommonCount_expectation_le` of [lean/OAI/Probability/Ballisticity/Estimates/CommonOccupationBound.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Estimates/CommonOccupationBound.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DirectionalTransience`, with `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal BigOperators Topology Classical`):
--
--   ```lean
--   theorem smallCommonCount_expectation_le {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
--       (hue : UniformElliptic ν) (e f : Direction d)
--       (htrans : DirectionallyTransient ν (realPosition (step e)))
--       {b R s c q L : ℝ} (hb : 0 ≤ b) (hR : b ≤ R) (hc : 0 ≤ c) (hq : 0 ≤ q)
--       (hbs : b ≤ 2*s) (K : ℕ) (hK : 0 < K) (k : ℝ → ℕ)
--       (hk : ∀ i : Lattice d × Lattice d, signedHeight e i.1=signedHeight e i.2 →
--         b < pairGap f i → pairGap f i < R → 0 < k (pairGap f i))
--       (hdrift : ∀ i : Lattice d × Lattice d, signedHeight e i.1=signedHeight e i.2 →
--         observedStateGain f b R c q i+observedStatePotential f b R i ≤
--         ∫ P, observedStatePotential f b R
--           (pairOrigin (commonCutObserver (realPosition (step e)) (fun j => pairGap f j < R)
--             (observedAdvanceRule e f b K k) P))
--           ∂sharedConditionedPairLaw ν (realPosition (step e)) i.1 i.2)
--       (hmean : ∀ i : Lattice d × Lattice d, signedHeight e i.1=signedHeight e i.2 →
--         (∫⁻ P, observedCharge e f b R s K k P
--           ∂sharedConditionedPairLaw ν (realPosition (step e)) i.1 i.2) ≤
--         ENNReal.ofReal L*ENNReal.ofReal (observedStateGain f b R c q i))
--       (H : ℕ) (i : Lattice d × Lattice d) (hi : signedHeight e i.1=signedHeight e i.2) :
--       (∫⁻ P, (smallCommonCount e f s H P : ℝ≥0∞)
--         ∂sharedConditionedPairLaw ν (realPosition (step e)) i.1 i.2) ≤
--         ENNReal.ofReal L*ENNReal.ofReal ((2*R)^((3:ℝ)/2)-observedStatePotential f b R i)+
--         H*sharedConditionedPairLaw ν (realPosition (step e)) i.1 i.2 (PhysicalGapExit e f R H i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.DirectionalTransience.signedHeight` (definitions bundle `OAIQ242Bal000` of this split); `OAI.DirectionalTransience.PhysicalGapExit` and `OAI.DirectionalTransience.sharedConditionedPairLaw` (definitions bundle `OAIQ242Bal002` of this split); `OAI.DirectionalTransience.commonCutObserver`, `OAI.DirectionalTransience.observedAdvanceRule`, `OAI.DirectionalTransience.observedStateGain`, `OAI.DirectionalTransience.observedStatePotential`, `OAI.DirectionalTransience.pairGap`, `OAI.DirectionalTransience.pairOrigin` and `OAI.DirectionalTransience.smallCommonCount` (definitions bundle `OAIQ242Bal003` of this split); `OAI.DirectionalTransience.observedCharge` (definitions bundle `OAIQ242Bal006` of this split); `OAI.DirectionalTransience.Direction`, `OAI.DirectionalTransience.DirectionallyTransient`, `OAI.DirectionalTransience.Lattice`, `OAI.DirectionalTransience.Path`, `OAI.DirectionalTransience.Row`, `OAI.DirectionalTransience.UniformElliptic`, `OAI.DirectionalTransience.realPosition` and `OAI.DirectionalTransience.step` (the published bundle `Def_DirectionalBallisticity`).
--
--   **Used by.** The proof of `OAI.DirectionalTransience.occupation_finite_bound` of this split imports it.
-- source:
--   OpenAI, Directional transience implies ballisticity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 220; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Estimates/CommonOccupationBound.lean (declaration OAI.DirectionalTransience.smallCommonCount_expectation_le)

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal006

section

attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedEndpointRaw_finite _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedProfile_measurableSpace _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

theorem smallCommonCount_expectation_le {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    {b R s c q L : ℝ} (hb : 0 ≤ b) (hR : b ≤ R) (hc : 0 ≤ c) (hq : 0 ≤ q)
    (hbs : b ≤ 2*s) (K : ℕ) (hK : 0 < K) (k : ℝ → ℕ)
    (hk : ∀ i : Lattice d × Lattice d, signedHeight e i.1=signedHeight e i.2 →
      b < pairGap f i → pairGap f i < R → 0 < k (pairGap f i))
    (hdrift : ∀ i : Lattice d × Lattice d, signedHeight e i.1=signedHeight e i.2 →
      observedStateGain f b R c q i+observedStatePotential f b R i ≤
      ∫ P, observedStatePotential f b R
        (pairOrigin (commonCutObserver (realPosition (step e)) (fun j => pairGap f j < R)
          (observedAdvanceRule e f b K k) P))
        ∂sharedConditionedPairLaw ν (realPosition (step e)) i.1 i.2)
    (hmean : ∀ i : Lattice d × Lattice d, signedHeight e i.1=signedHeight e i.2 →
      (∫⁻ P, observedCharge e f b R s K k P
        ∂sharedConditionedPairLaw ν (realPosition (step e)) i.1 i.2) ≤
      ENNReal.ofReal L*ENNReal.ofReal (observedStateGain f b R c q i))
    (H : ℕ) (i : Lattice d × Lattice d) (hi : signedHeight e i.1=signedHeight e i.2) :
    (∫⁻ P, (smallCommonCount e f s H P : ℝ≥0∞)
      ∂sharedConditionedPairLaw ν (realPosition (step e)) i.1 i.2) ≤
      ENNReal.ofReal L*ENNReal.ofReal ((2*R)^((3:ℝ)/2)-observedStatePotential f b R i)+
      H*sharedConditionedPairLaw ν (realPosition (step e)) i.1 i.2 (PhysicalGapExit e f R H i) := by
  sorry

end DirectionalTransience

end

end

end OAI
end
