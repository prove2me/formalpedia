-- Prove2me | Theorems.Thm_OAI_DirectionalTransience_conditioned_wordRadius_integrable
-- name    : OAI.DirectionalTransience.conditioned_wordRadius_integrable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:53:20.118604+00:00
-- url     : https://prove2.me/theorems/09380dcf-046e-44c0-9442-2f554317b185
-- title:
--   OAI.DirectionalTransience.conditioned_wordRadius_integrable: intermediate lemma from OpenAI, Directional transience implies ballisticity
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectionalTransience.directional_transience_implies_ballisticity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Directional transience implies ballisticity*, OpenAI Math Release, September 23, 2026, result family 220, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DirectionalTransience.conditioned_wordRadius_integrable` of [lean/OAI/Probability/Ballisticity/Geometry/WordCoordinate.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Geometry/WordCoordinate.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DirectionalTransience`, with `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal BigOperators Topology`):
--
--   ```lean
--   lemma conditioned_wordRadius_integrable {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
--       (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
--       (htrans : DirectionallyTransient ν ℓ) :
--       Integrable (fun X => wordRadius (firstWord ℓ X)) (conditionedLaw ν ℓ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.DirectionalTransience.conditionedLaw` and `OAI.DirectionalTransience.firstWord` (definitions bundle `OAIQ242Bal000` of this split); `OAI.DirectionalTransience.wordRadius` (definitions bundle `OAIQ242Bal002` of this split); `OAI.DirectionalTransience.Direction`, `OAI.DirectionalTransience.DirectionallyTransient`, `OAI.DirectionalTransience.Lattice`, `OAI.DirectionalTransience.Path`, `OAI.DirectionalTransience.Row`, `OAI.DirectionalTransience.UniformElliptic`, `OAI.DirectionalTransience.Vector` and `OAI.DirectionalTransience.dot` (the published bundle `Def_DirectionalBallisticity`).
--
--   **Used by.** The proofs of `OAI.DirectionalTransience.actual_outward_log_bound`, `OAI.DirectionalTransience.bad_radius_lower_escape_uniform`, `OAI.DirectionalTransience.clipped_pair_favorable_fraction`, `OAI.DirectionalTransience.directional_transience_implies_ballisticity`, `OAI.DirectionalTransience.independent_commonWordIncrement_integrable`, `OAI.DirectionalTransience.operational_constants_exist`, `OAI.DirectionalTransience.recordFluctuationScale_tendsto`, `OAI.DirectionalTransience.recordMedianSlope_small`, `OAI.DirectionalTransience.seed_block_tests`, `OAI.DirectionalTransience.shared_median_pair_path_limit`, `OAI.DirectionalTransience.spatial_confinement`, `OAI.DirectionalTransience.transverse_bad_radius_spread`, `OAI.DirectionalTransience.transverse_firstHit_fixed_sum_error`, `OAI.DirectionalTransience.transverse_firstHit_linear_path_limit` and `OAI.DirectionalTransience.transverse_firstHit_path_limit` of this split import it.
-- source:
--   OpenAI, Directional transience implies ballisticity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 220; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Geometry/WordCoordinate.lean (declaration OAI.DirectionalTransience.conditioned_wordRadius_integrable)

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal002

section

attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.continuousPathMeasurableSpace _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

lemma conditioned_wordRadius_integrable {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ) :
    Integrable (fun X => wordRadius (firstWord ℓ X)) (conditionedLaw ν ℓ) := by
  sorry

end DirectionalTransience
end
end

end OAI
end
