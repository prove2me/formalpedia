-- Prove2me | Theorems.Thm_OAI_DirectionalTransience_clipping_uniform
-- name    : OAI.DirectionalTransience.clipping_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:52:33.393201+00:00
-- url     : https://prove2.me/theorems/aecfa90b-1686-45ac-a427-1fc10013cc44
-- title:
--   OAI.DirectionalTransience.clipping_uniform: intermediate lemma from OpenAI, Directional transience implies ballisticity
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectionalTransience.directional_transience_implies_ballisticity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Directional transience implies ballisticity*, OpenAI Math Release, September 23, 2026, result family 220, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DirectionalTransience.clipping_uniform` of [lean/OAI/Probability/Ballisticity/Estimates/UniformLowerMass.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Estimates/UniformLowerMass.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DirectionalTransience`, with `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal Topology Classical`):
--
--   ```lean
--   theorem clipping_uniform {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
--       (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
--       (htrans : DirectionallyTransient ν (realPosition (step e)))
--       {T η ε : ℝ} (hT : 0 < T) (hη : 0 < η) (hε : 0 < ε) :
--       ∃ c : ℝ≥0∞, 0 < c ∧ c ≤ 1 ∧ ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, R ≤ r → ∃ θ : ℝ,
--         ∀ (x : Lattice d) (H : ℕ), (H:ℝ) ≤ T*fluctuationScale
--           (independentConditionedPairLaw ν (realPosition (step e)))
--           (commonIncrementProcess (realPosition (step e)) f 0) r →
--         (environmentLaw ν).real {ω | quenchedKernel (ω,x)
--           (TubePrefix (realPosition (step e)) f x θ (η*r) H) < c} < ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.DirectionalTransience.commonIncrementProcess`, `OAI.DirectionalTransience.fluctuationScale`, `OAI.DirectionalTransience.independentConditionedPairLaw` and `OAI.DirectionalTransience.quenchedKernel` (definitions bundle `OAIQ242Bal000` of this split); `OAI.DirectionalTransience.TubePrefix` (definitions bundle `OAIQ242Bal002` of this split); `OAI.DirectionalTransience.Direction`, `OAI.DirectionalTransience.DirectionallyTransient`, `OAI.DirectionalTransience.Environment`, `OAI.DirectionalTransience.Lattice`, `OAI.DirectionalTransience.Path`, `OAI.DirectionalTransience.Row`, `OAI.DirectionalTransience.State`, `OAI.DirectionalTransience.UniformElliptic`, `OAI.DirectionalTransience.environmentLaw`, `OAI.DirectionalTransience.realPosition` and `OAI.DirectionalTransience.step` (the published bundle `Def_DirectionalBallisticity`).
--
--   **Used by.** The proofs of `OAI.DirectionalTransience.actual_consumed_cell_failure`, `OAI.DirectionalTransience.clipped_pair_favorable_fraction` and `OAI.DirectionalTransience.seed_block_tests` of this split import it.
-- source:
--   OpenAI, Directional transience implies ballisticity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 220; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Estimates/UniformLowerMass.lean (declaration OAI.DirectionalTransience.clipping_uniform)

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
open scoped ENNReal NNReal Topology Classical
namespace DirectionalTransience

theorem clipping_uniform {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e)))
    {T η ε : ℝ} (hT : 0 < T) (hη : 0 < η) (hε : 0 < ε) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≤ 1 ∧ ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, R ≤ r → ∃ θ : ℝ,
      ∀ (x : Lattice d) (H : ℕ), (H:ℝ) ≤ T*fluctuationScale
        (independentConditionedPairLaw ν (realPosition (step e)))
        (commonIncrementProcess (realPosition (step e)) f 0) r →
      (environmentLaw ν).real {ω | quenchedKernel (ω,x)
        (TubePrefix (realPosition (step e)) f x θ (η*r) H) < c} < ε := by
  sorry
end DirectionalTransience

end

end

end OAI
end
