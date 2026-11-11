-- Prove2me | Theorems.Thm_OAI_DirectionalTransience_shared_uniform_good_shrinking
-- name    : OAI.DirectionalTransience.shared_uniform_good_shrinking
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:55:55.516957+00:00
-- url     : https://prove2.me/theorems/5e9ce911-2a34-451a-a655-9ffaa1329eb2
-- title:
--   OAI.DirectionalTransience.shared_uniform_good_shrinking: intermediate lemma from OpenAI, Directional transience implies ballisticity
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectionalTransience.directional_transience_implies_ballisticity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Directional transience implies ballisticity*, OpenAI Math Release, September 23, 2026, result family 220, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DirectionalTransience.shared_uniform_good_shrinking` of [lean/OAI/Probability/Ballisticity/Estimates/SharedShrinking.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Estimates/SharedShrinking.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DirectionalTransience`, with `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal BigOperators Topology Classical`):
--
--   ```lean
--   theorem shared_uniform_good_shrinking {d : ℕ} (ν : Measure (Row d))
--       [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
--       (htrans : DirectionallyTransient ν (realPosition (step e)))
--       {t : ℝ} (ht : 0 < t) :
--       let ℓ := realPosition (step e)
--       let μ := independentConditionedPairLaw ν ℓ
--       let n := fluctuationScale μ (commonIncrementProcess ℓ f 0)
--       ∃ l ε R : ℝ, 0 < l ∧ l < 1 ∧ 0 < ε ∧ 0 < R ∧
--         ∀ u : ℝ, R ≤ u → n u * μ.real {P | l*u < |commonIncrementProcess ℓ f 0 P|} ≤ ε →
--         ∀ x y : Lattice d, signedHeight e x = signedHeight e y → |signedCoordinate f (x-y)| = u →
--         (sharedConditionedPairLaw ν ℓ x y).real
--           {P | ∃ h ≤ ⌊t*n u⌋₊, |physicalFirstHitGap ℓ f x y h P| ≤ u/2} ≤
--             8*Real.exp (-commonMeanWidth ν ℓ/(16*t))
--   ```
--
--   **Definitions.** The statement is written with `OAI.DirectionalTransience.commonIncrementProcess`, `OAI.DirectionalTransience.fluctuationScale`, `OAI.DirectionalTransience.independentConditionedPairLaw`, `OAI.DirectionalTransience.signedCoordinate` and `OAI.DirectionalTransience.signedHeight` (definitions bundle `OAIQ242Bal000` of this split); `OAI.DirectionalTransience.commonMeanWidth`, `OAI.DirectionalTransience.physicalFirstHitGap` and `OAI.DirectionalTransience.sharedConditionedPairLaw` (definitions bundle `OAIQ242Bal002` of this split); `OAI.DirectionalTransience.Direction`, `OAI.DirectionalTransience.DirectionallyTransient`, `OAI.DirectionalTransience.Lattice`, `OAI.DirectionalTransience.Path`, `OAI.DirectionalTransience.Row`, `OAI.DirectionalTransience.UniformElliptic`, `OAI.DirectionalTransience.Vector`, `OAI.DirectionalTransience.realPosition` and `OAI.DirectionalTransience.step` (the published bundle `Def_DirectionalBallisticity`).
--
--   **Used by.** The proof of `OAI.DirectionalTransience.exists_occupationData` of this split imports it.
-- source:
--   OpenAI, Directional transience implies ballisticity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 220; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Estimates/SharedShrinking.lean (declaration OAI.DirectionalTransience.shared_uniform_good_shrinking)

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal002

section

attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

theorem shared_uniform_good_shrinking {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    {t : ℝ} (ht : 0 < t) :
    let ℓ := realPosition (step e)
    let μ := independentConditionedPairLaw ν ℓ
    let n := fluctuationScale μ (commonIncrementProcess ℓ f 0)
    ∃ l ε R : ℝ, 0 < l ∧ l < 1 ∧ 0 < ε ∧ 0 < R ∧
      ∀ u : ℝ, R ≤ u → n u * μ.real {P | l*u < |commonIncrementProcess ℓ f 0 P|} ≤ ε →
      ∀ x y : Lattice d, signedHeight e x = signedHeight e y → |signedCoordinate f (x-y)| = u →
      (sharedConditionedPairLaw ν ℓ x y).real
        {P | ∃ h ≤ ⌊t*n u⌋₊, |physicalFirstHitGap ℓ f x y h P| ≤ u/2} ≤
          8*Real.exp (-commonMeanWidth ν ℓ/(16*t)) := by
  sorry

end DirectionalTransience

end

end

end OAI
end
