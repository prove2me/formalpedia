-- Prove2me | Theorems.Thm_OAI_DirectionalTransience_seed_block_tests
-- name    : OAI.DirectionalTransience.seed_block_tests
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:53:50.279096+00:00
-- url     : https://prove2.me/theorems/1620b5dc-2543-45ea-96e0-87f2fe56618d
-- title:
--   OAI.DirectionalTransience.seed_block_tests: intermediate lemma from OpenAI, Directional transience implies ballisticity
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectionalTransience.directional_transience_implies_ballisticity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Directional transience implies ballisticity*, OpenAI Math Release, September 23, 2026, result family 220, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DirectionalTransience.seed_block_tests` of [lean/OAI/Probability/Ballisticity/Coupling/SeedProfile.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Coupling/SeedProfile.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DirectionalTransience`, with `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal BigOperators Topology Classical`):
--
--   ```lean
--   theorem seed_block_tests {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
--       (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
--       (htrans : DirectionallyTransient ν (realPosition (step e))) :
--       ∃ a j : ℝ, 0 < a ∧ 0 < j ∧ j ≤ 1/2 ∧
--         ∀ T η ε : ℝ, 0 < T → 0 < η → 0 < ε →
--         ∃ c R : ℝ, 0 < c ∧ 0 < R ∧ ∀ r : ℝ, R ≤ r →
--         let n := fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
--           (commonIncrementProcess (realPosition (step e)) f 0) r
--         0 < ⌊n⌋₊ ∧ ∃ θ : ℝ, ∃ s : ℤ, (s=1 ∨ s= -1) ∧
--         (∀ (H : ℕ) (μ : ProbabilityMeasure (Lattice d)), (H:ℝ) ≤ T*n →
--           (environmentLaw ν).real {ω | (seedEndpointRaw e H (SeedCentral f H θ (η*r)) μ.toMeasure ω Set.univ).toReal < c} ≤ ε) ∧
--         (∀ μ : ProbabilityMeasure (Lattice d), j ≤ (environmentLaw ν).real
--           {ω | j ≤ (seedEndpointRaw e ⌊n⌋₊ (SeedJump f ⌊n⌋₊ s θ (a*r)) μ.toMeasure ω Set.univ).toReal})
--   ```
--
--   **Definitions.** The statement is written with `OAI.DirectionalTransience.commonIncrementProcess`, `OAI.DirectionalTransience.fluctuationScale` and `OAI.DirectionalTransience.independentConditionedPairLaw` (definitions bundle `OAIQ242Bal000` of this split); `OAI.DirectionalTransience.SeedCentral`, `OAI.DirectionalTransience.SeedJump` and `OAI.DirectionalTransience.seedEndpointRaw` (definitions bundle `OAIQ242Bal002` of this split); `OAI.DirectionalTransience.Direction`, `OAI.DirectionalTransience.DirectionallyTransient`, `OAI.DirectionalTransience.Environment`, `OAI.DirectionalTransience.Lattice`, `OAI.DirectionalTransience.Path`, `OAI.DirectionalTransience.Row`, `OAI.DirectionalTransience.UniformElliptic`, `OAI.DirectionalTransience.environmentLaw`, `OAI.DirectionalTransience.realPosition` and `OAI.DirectionalTransience.step` (the published bundle `Def_DirectionalBallisticity`).
--
--   **Used by.** The proof of `OAI.DirectionalTransience.seed_mass_at_scale` of this split imports it.
-- source:
--   OpenAI, Directional transience implies ballisticity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 220; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Coupling/SeedProfile.lean (declaration OAI.DirectionalTransience.seed_block_tests)

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal002

section

attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

theorem seed_block_tests {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ a j : ℝ, 0 < a ∧ 0 < j ∧ j ≤ 1/2 ∧
      ∀ T η ε : ℝ, 0 < T → 0 < η → 0 < ε →
      ∃ c R : ℝ, 0 < c ∧ 0 < R ∧ ∀ r : ℝ, R ≤ r →
      let n := fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
        (commonIncrementProcess (realPosition (step e)) f 0) r
      0 < ⌊n⌋₊ ∧ ∃ θ : ℝ, ∃ s : ℤ, (s=1 ∨ s= -1) ∧
      (∀ (H : ℕ) (μ : ProbabilityMeasure (Lattice d)), (H:ℝ) ≤ T*n →
        (environmentLaw ν).real {ω | (seedEndpointRaw e H (SeedCentral f H θ (η*r)) μ.toMeasure ω Set.univ).toReal < c} ≤ ε) ∧
      (∀ μ : ProbabilityMeasure (Lattice d), j ≤ (environmentLaw ν).real
        {ω | j ≤ (seedEndpointRaw e ⌊n⌋₊ (SeedJump f ⌊n⌋₊ s θ (a*r)) μ.toMeasure ω Set.univ).toReal}) := by
  sorry

end DirectionalTransience

end

end OAI
end
