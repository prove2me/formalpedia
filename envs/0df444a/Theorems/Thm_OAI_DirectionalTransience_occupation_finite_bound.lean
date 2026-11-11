-- Prove2me | Theorems.Thm_OAI_DirectionalTransience_occupation_finite_bound
-- name    : OAI.DirectionalTransience.occupation_finite_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:54:06.937358+00:00
-- url     : https://prove2.me/theorems/098101d5-e5f8-40fc-976a-c6dce4bd832e
-- title:
--   OAI.DirectionalTransience.occupation_finite_bound: intermediate lemma from OpenAI, Directional transience implies ballisticity
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectionalTransience.directional_transience_implies_ballisticity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Directional transience implies ballisticity*, OpenAI Math Release, September 23, 2026, result family 220, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DirectionalTransience.occupation_finite_bound` of [lean/OAI/Probability/Ballisticity/Estimates/CommonOccupationBound.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Estimates/CommonOccupationBound.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DirectionalTransience`, with `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal BigOperators Topology Classical`):
--
--   ```lean
--   theorem occupation_finite_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
--       (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
--       (htrans : DirectionallyTransient ν (realPosition (step e)))
--       {t : ℝ} (ht : 0 < t) (D : OccupationData ν e f t)
--       {b r ρ A : ℝ} (hb : D.u₀ ≤ b) (hbr : b ≤ r) (hρ : 0 ≤ ρ) (hA : 1 ≤ A)
--       (hbs : b ≤ 2*(ρ*r))
--       (hg : ∀ u, b ≤ u → u ≤ A*r → fluctuationScale
--         (independentConditionedPairLaw ν (realPosition (step e)))
--         (commonIncrementProcess (realPosition (step e)) f 0) u*
--         (independentConditionedPairLaw ν (realPosition (step e))).real
--           {P | D.l*u < |commonIncrementProcess (realPosition (step e)) f 0 P|} ≤ D.ε)
--       (K : ℕ) (hK : 0 < K)
--       (hKn : (K:ℝ) ≤ D.C*fluctuationScale
--         (independentConditionedPairLaw ν (realPosition (step e)))
--         (commonIncrementProcess (realPosition (step e)) f 0) b)
--       (hKprob : ∀ x y : Lattice d, signedHeight e x=signedHeight e y →
--         D.q ≤ (sharedConditionedPairLaw ν (realPosition (step e)) x y).real
--           (layerPairTruthEvent (realPosition (step e)) (signedHeight e) x y
--             (signedHeight e x+K) {uv | 2*b ≤ |signedCoordinate f uv.1-signedCoordinate f uv.2|}))
--       (H : ℕ) (i : Lattice d × Lattice d) (hi : signedHeight e i.1=signedHeight e i.2) :
--       let ℓ := realPosition (step e)
--       let n := fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0)
--       let M := 128*commonMeanWidth ν ℓ
--       let δ := 8*Real.exp (-commonMeanWidth ν ℓ/(16*t))
--       let J := max ((2:ℝ)^((7:ℝ)/4)) (A^2)*n r/r^((3:ℝ)/2)
--       (∫⁻ P, (smallCommonCount e f (ρ*r) H P : ℝ≥0∞) ∂sharedConditionedPairLaw ν ℓ i.1 i.2) ≤
--         ENNReal.ofReal (occupationCoefficient J D.C D.q M b r ρ A δ*(2*(A*r))^((3:ℝ)/2))+
--           H*sharedConditionedPairLaw ν ℓ i.1 i.2 (PhysicalGapExit e f (A*r) H i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.DirectionalTransience.commonIncrementProcess`, `OAI.DirectionalTransience.fluctuationScale`, `OAI.DirectionalTransience.independentConditionedPairLaw`, `OAI.DirectionalTransience.signedCoordinate` and `OAI.DirectionalTransience.signedHeight` (definitions bundle `OAIQ242Bal000` of this split); `OAI.DirectionalTransience.occupationCoefficient` (definitions bundle `OAIQ242Bal001` of this split); `OAI.DirectionalTransience.OccupationData`, `OAI.DirectionalTransience.PhysicalGapExit`, `OAI.DirectionalTransience.commonMeanWidth`, `OAI.DirectionalTransience.layerPairTruthEvent` and `OAI.DirectionalTransience.sharedConditionedPairLaw` (definitions bundle `OAIQ242Bal002` of this split); `OAI.DirectionalTransience.smallCommonCount` (definitions bundle `OAIQ242Bal003` of this split); `OAI.DirectionalTransience.Direction`, `OAI.DirectionalTransience.DirectionallyTransient`, `OAI.DirectionalTransience.Lattice`, `OAI.DirectionalTransience.Path`, `OAI.DirectionalTransience.Row`, `OAI.DirectionalTransience.UniformElliptic`, `OAI.DirectionalTransience.Vector`, `OAI.DirectionalTransience.realPosition` and `OAI.DirectionalTransience.step` (the published bundle `Def_DirectionalBallisticity`).
--
--   **Used by.** The proof of `OAI.DirectionalTransience.shared_first_hit_occupation_vanishes` of this split imports it.
-- source:
--   OpenAI, Directional transience implies ballisticity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 220; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Estimates/CommonOccupationBound.lean (declaration OAI.DirectionalTransience.occupation_finite_bound)

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal002
import Definitions.Def_OAIQ242Bal003

section

attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.curveEndpoint_finite _root_.OAI.DirectionalTransience.curveIncrement_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

theorem occupation_finite_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    {t : ℝ} (ht : 0 < t) (D : OccupationData ν e f t)
    {b r ρ A : ℝ} (hb : D.u₀ ≤ b) (hbr : b ≤ r) (hρ : 0 ≤ ρ) (hA : 1 ≤ A)
    (hbs : b ≤ 2*(ρ*r))
    (hg : ∀ u, b ≤ u → u ≤ A*r → fluctuationScale
      (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) u*
      (independentConditionedPairLaw ν (realPosition (step e))).real
        {P | D.l*u < |commonIncrementProcess (realPosition (step e)) f 0 P|} ≤ D.ε)
    (K : ℕ) (hK : 0 < K)
    (hKn : (K:ℝ) ≤ D.C*fluctuationScale
      (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) b)
    (hKprob : ∀ x y : Lattice d, signedHeight e x=signedHeight e y →
      D.q ≤ (sharedConditionedPairLaw ν (realPosition (step e)) x y).real
        (layerPairTruthEvent (realPosition (step e)) (signedHeight e) x y
          (signedHeight e x+K) {uv | 2*b ≤ |signedCoordinate f uv.1-signedCoordinate f uv.2|}))
    (H : ℕ) (i : Lattice d × Lattice d) (hi : signedHeight e i.1=signedHeight e i.2) :
    let ℓ := realPosition (step e)
    let n := fluctuationScale (independentConditionedPairLaw ν ℓ) (commonIncrementProcess ℓ f 0)
    let M := 128*commonMeanWidth ν ℓ
    let δ := 8*Real.exp (-commonMeanWidth ν ℓ/(16*t))
    let J := max ((2:ℝ)^((7:ℝ)/4)) (A^2)*n r/r^((3:ℝ)/2)
    (∫⁻ P, (smallCommonCount e f (ρ*r) H P : ℝ≥0∞) ∂sharedConditionedPairLaw ν ℓ i.1 i.2) ≤
      ENNReal.ofReal (occupationCoefficient J D.C D.q M b r ρ A δ*(2*(A*r))^((3:ℝ)/2))+
        H*sharedConditionedPairLaw ν ℓ i.1 i.2 (PhysicalGapExit e f (A*r) H i) := by
  sorry

end DirectionalTransience

end

end

end OAI
end
