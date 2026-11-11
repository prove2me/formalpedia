-- Prove2me | Theorems.Thm_OAI_DirectionalTransience_bad_radius_lower_escape_uniform
-- name    : OAI.DirectionalTransience.bad_radius_lower_escape_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:54:13.565934+00:00
-- url     : https://prove2.me/theorems/6fe49ce6-a6ff-4ac2-aa45-13619584d124
-- title:
--   OAI.DirectionalTransience.bad_radius_lower_escape_uniform: intermediate lemma from OpenAI, Directional transience implies ballisticity
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectionalTransience.directional_transience_implies_ballisticity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Directional transience implies ballisticity*, OpenAI Math Release, September 23, 2026, result family 220, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DirectionalTransience.bad_radius_lower_escape_uniform` of [lean/OAI/Probability/Ballisticity/Crossings/UniformLowerCutoff.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Crossings/UniformLowerCutoff.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DirectionalTransience`, with `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal BigOperators Topology Classical`):
--
--   ```lean
--   theorem bad_radius_lower_escape_uniform {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
--       (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
--       (htrans : DirectionallyTransient ν (realPosition (step e)))
--       {l ε : ℝ} (hl : 0 < l) (hl1 : l ≤ 1) (hε : 0 < ε) :
--       ∃ C q D₀ : ℝ, 0 < C ∧ 0 < q ∧ 0 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
--         ε ≤ fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
--           (commonIncrementProcess (realPosition (step e)) f 0) D*
--           (independentConditionedPairLaw ν (realPosition (step e))).real
--             {P | l*D < |commonIncrementProcess (realPosition (step e)) f 0 P|} →
--         LowerEscape ν e f (4*D) C q
--   ```
--
--   **Definitions.** The statement is written with `OAI.DirectionalTransience.commonIncrementProcess`, `OAI.DirectionalTransience.fluctuationScale` and `OAI.DirectionalTransience.independentConditionedPairLaw` (definitions bundle `OAIQ242Bal000` of this split); `OAI.DirectionalTransience.LowerEscape` (definitions bundle `OAIQ242Bal002` of this split); `OAI.DirectionalTransience.Direction`, `OAI.DirectionalTransience.DirectionallyTransient`, `OAI.DirectionalTransience.Lattice`, `OAI.DirectionalTransience.Path`, `OAI.DirectionalTransience.Row`, `OAI.DirectionalTransience.UniformElliptic`, `OAI.DirectionalTransience.realPosition` and `OAI.DirectionalTransience.step` (the published bundle `Def_DirectionalBallisticity`).
--
--   **Used by.** The proof of `OAI.DirectionalTransience.exists_occupationData` of this split imports it.
-- source:
--   OpenAI, Directional transience implies ballisticity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 220; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Crossings/UniformLowerCutoff.lean (declaration OAI.DirectionalTransience.bad_radius_lower_escape_uniform)

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

theorem bad_radius_lower_escape_uniform {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    {l ε : ℝ} (hl : 0 < l) (hl1 : l ≤ 1) (hε : 0 < ε) :
    ∃ C q D₀ : ℝ, 0 < C ∧ 0 < q ∧ 0 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
      ε ≤ fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
        (commonIncrementProcess (realPosition (step e)) f 0) D*
        (independentConditionedPairLaw ν (realPosition (step e))).real
          {P | l*D < |commonIncrementProcess (realPosition (step e)) f 0 P|} →
      LowerEscape ν e f (4*D) C q := by
  sorry

end DirectionalTransience

end

end

end OAI
end
