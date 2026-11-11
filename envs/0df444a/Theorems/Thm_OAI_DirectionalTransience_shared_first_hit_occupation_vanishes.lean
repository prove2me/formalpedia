-- Prove2me | Theorems.Thm_OAI_DirectionalTransience_shared_first_hit_occupation_vanishes
-- name    : OAI.DirectionalTransience.shared_first_hit_occupation_vanishes
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:00:47.309226+00:00
-- url     : https://prove2.me/theorems/f2a5ce1f-b44e-418b-bebd-0c56463b47cf
-- title:
--   OAI.DirectionalTransience.shared_first_hit_occupation_vanishes: intermediate lemma from OpenAI, Directional transience implies ballisticity
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectionalTransience.directional_transience_implies_ballisticity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Directional transience implies ballisticity*, OpenAI Math Release, September 23, 2026, result family 220, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DirectionalTransience.shared_first_hit_occupation_vanishes` of [lean/OAI/Probability/Ballisticity/Estimates/OccupationLimit.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Estimates/OccupationLimit.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DirectionalTransience`, with `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal BigOperators Topology Classical`):
--
--   ```lean
--   theorem shared_first_hit_occupation_vanishes {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
--       (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
--       (htrans : DirectionallyTransient ν (realPosition (step e)))
--       (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
--         (commonIncrementProcess (realPosition (step e)) f 0) r)
--       (x : ℕ → Lattice d) {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε) :
--       ∃ ρ : ℝ, 0 < ρ ∧
--         let n := fun i => fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
--           (commonIncrementProcess (realPosition (step e)) f 0) (r i)
--         ∀ᶠ i in atTop, firstHitOccupationMean ν e f (x i) (x i) (ρ*r i) (⌊T*n i⌋₊+1)/n i ≤ ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.DirectionalTransience.commonIncrementProcess`, `OAI.DirectionalTransience.fluctuationScale` and `OAI.DirectionalTransience.independentConditionedPairLaw` (definitions bundle `OAIQ242Bal000` of this split); `OAI.DirectionalTransience.IsGaussianSequence` (definitions bundle `OAIQ242Bal002` of this split); `OAI.DirectionalTransience.firstHitOccupationMean` (definitions bundle `OAIQ242Bal006` of this split); `OAI.DirectionalTransience.Direction`, `OAI.DirectionalTransience.DirectionallyTransient`, `OAI.DirectionalTransience.Lattice`, `OAI.DirectionalTransience.Path`, `OAI.DirectionalTransience.Row`, `OAI.DirectionalTransience.UniformElliptic`, `OAI.DirectionalTransience.realPosition` and `OAI.DirectionalTransience.step` (the published bundle `Def_DirectionalBallisticity`).
--
--   **Used by.** The proof of `OAI.DirectionalTransience.shared_pair_path_limit` of this split imports it.
-- source:
--   OpenAI, Directional transience implies ballisticity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 220; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Estimates/OccupationLimit.lean (declaration OAI.DirectionalTransience.shared_first_hit_occupation_vanishes)

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

theorem shared_first_hit_occupation_vanishes {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    (r : ℕ → ℝ) (hr : IsGaussianSequence (independentConditionedPairLaw ν (realPosition (step e)))
      (commonIncrementProcess (realPosition (step e)) f 0) r)
    (x : ℕ → Lattice d) {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧
      let n := fun i => fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
        (commonIncrementProcess (realPosition (step e)) f 0) (r i)
      ∀ᶠ i in atTop, firstHitOccupationMean ν e f (x i) (x i) (ρ*r i) (⌊T*n i⌋₊+1)/n i ≤ ε := by
  sorry

end DirectionalTransience

end

end

end OAI
end
