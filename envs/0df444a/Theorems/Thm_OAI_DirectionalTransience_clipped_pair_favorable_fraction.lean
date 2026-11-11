-- Prove2me | Theorems.Thm_OAI_DirectionalTransience_clipped_pair_favorable_fraction
-- name    : OAI.DirectionalTransience.clipped_pair_favorable_fraction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:57:51.84163+00:00
-- url     : https://prove2.me/theorems/311ada5e-76a5-43b2-81e4-1f837689a406
-- title:
--   OAI.DirectionalTransience.clipped_pair_favorable_fraction: intermediate lemma from OpenAI, Directional transience implies ballisticity
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectionalTransience.directional_transience_implies_ballisticity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Directional transience implies ballisticity*, OpenAI Math Release, September 23, 2026, result family 220, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DirectionalTransience.clipped_pair_favorable_fraction` of [lean/OAI/Probability/Ballisticity/Walk/ClippedPairGrowth.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Walk/ClippedPairGrowth.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DirectionalTransience`, with `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal NNReal BigOperators Topology Classical`):
--
--   ```lean
--   theorem clipped_pair_favorable_fraction {d : ℕ} (ν : Measure (Row d))
--       [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
--       (htrans : DirectionallyTransient ν (realPosition (step e))) :
--       ∃ a j c : ℝ, 0 < a ∧ 0 < j ∧ 0 < c ∧ ∀ δ : ℝ, 0 < δ →
--         ∃ d₀ R : ℝ, 0 < d₀ ∧ 0 < R ∧ ∀ r : ℝ, R ≤ r →
--           let H := ⌊fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
--             (commonIncrementProcess (realPosition (step e)) f 0) r⌋₊
--           0 < H ∧ ∃ θ s : ℝ, (s=1 ∨ s= -1) ∧
--           ∀ π : Measure (Lattice d × Lattice d), IsProbabilityMeasure π →
--           c ≤ (environmentLaw ν).real {ω | c ≤ ∫ x,
--             if j ≤ jumpPrefixMass (realPosition (step e)) f ((H:ℝ)*θ) (a*r) s H ω
--                 (if s=1 then x.2 else x.1) ∧
--               d₀ ≤ centralPrefixMass (realPosition (step e)) f θ (δ*r) H ω x.1 ∧
--               d₀ ≤ centralPrefixMass (realPosition (step e)) f θ (δ*r) H ω x.2
--             then (1:ℝ) else 0 ∂π}
--   ```
--
--   **Definitions.** The statement is written with `OAI.DirectionalTransience.commonIncrementProcess`, `OAI.DirectionalTransience.fluctuationScale` and `OAI.DirectionalTransience.independentConditionedPairLaw` (definitions bundle `OAIQ242Bal000` of this split); `OAI.DirectionalTransience.jumpPrefixMass` (definitions bundle `OAIQ242Bal003` of this split); `OAI.DirectionalTransience.centralPrefixMass` (definitions bundle `OAIQ242Bal005` of this split); `OAI.DirectionalTransience.Direction`, `OAI.DirectionalTransience.DirectionallyTransient`, `OAI.DirectionalTransience.Environment`, `OAI.DirectionalTransience.Lattice`, `OAI.DirectionalTransience.Path`, `OAI.DirectionalTransience.Row`, `OAI.DirectionalTransience.UniformElliptic`, `OAI.DirectionalTransience.environmentLaw`, `OAI.DirectionalTransience.realPosition` and `OAI.DirectionalTransience.step` (the published bundle `Def_DirectionalBallisticity`).
--
--   **Used by.** The proof of `OAI.DirectionalTransience.actual_buffer_excess` of this split imports it.
-- source:
--   OpenAI, Directional transience implies ballisticity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 220; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Walk/ClippedPairGrowth.lean (declaration OAI.DirectionalTransience.clipped_pair_favorable_fraction)

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal005

section

attribute [-instance] _root_.OAI.DirectionalTransience.SeedProfile.probability _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleEndpointLaw_finite _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.rawTupleWordLaw_finite _root_.OAI.DirectionalTransience.rawWordLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetEndpointLaw_finite _root_.OAI.DirectionalTransience.relativeBudgetWordLaw_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite _root_.OAI.DirectionalTransience.variableHitKernel_finite
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

theorem clipped_pair_favorable_fraction {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ a j c : ℝ, 0 < a ∧ 0 < j ∧ 0 < c ∧ ∀ δ : ℝ, 0 < δ →
      ∃ d₀ R : ℝ, 0 < d₀ ∧ 0 < R ∧ ∀ r : ℝ, R ≤ r →
        let H := ⌊fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
          (commonIncrementProcess (realPosition (step e)) f 0) r⌋₊
        0 < H ∧ ∃ θ s : ℝ, (s=1 ∨ s= -1) ∧
        ∀ π : Measure (Lattice d × Lattice d), IsProbabilityMeasure π →
        c ≤ (environmentLaw ν).real {ω | c ≤ ∫ x,
          if j ≤ jumpPrefixMass (realPosition (step e)) f ((H:ℝ)*θ) (a*r) s H ω
              (if s=1 then x.2 else x.1) ∧
            d₀ ≤ centralPrefixMass (realPosition (step e)) f θ (δ*r) H ω x.1 ∧
            d₀ ≤ centralPrefixMass (realPosition (step e)) f θ (δ*r) H ω x.2
          then (1:ℝ) else 0 ∂π} := by
  sorry
end DirectionalTransience

end

end

end OAI
end
