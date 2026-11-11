-- Prove2me | Theorems.Thm_OAI_DirectionalTransience_actual_cell_no_success
-- name    : OAI.DirectionalTransience.actual_cell_no_success
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:02:41.049683+00:00
-- url     : https://prove2.me/theorems/b466e724-8a5b-4c45-b5b9-70c2ce977df0
-- title:
--   OAI.DirectionalTransience.actual_cell_no_success: intermediate lemma from OpenAI, Directional transience implies ballisticity
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectionalTransience.directional_transience_implies_ballisticity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Directional transience implies ballisticity*, OpenAI Math Release, September 23, 2026, result family 220, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DirectionalTransience.actual_cell_no_success` of [lean/OAI/Probability/Ballisticity/Estimates/ScheduledCellSuccess.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Estimates/ScheduledCellSuccess.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DirectionalTransience`, with `open MeasureTheory ProbabilityTheory`, `open scoped ENNReal BigOperators Classical`):
--
--   ```lean
--   theorem actual_cell_no_success {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
--       (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
--       (htrans : DirectionallyTransient ν (realPosition (step e))) :
--       ∃ A : ℝ, 1 ≤ A ∧ ∀ k : ℕ, 2 ≤ k →
--         ∃ C c g₀ g₁ : ℝ, 0 < C ∧ ∃ hc : 0 < c, c ≤ 1 ∧ 0 < g₀ ∧ 0 < g₁ ∧
--         ∃ s : ℕ, 0 < s ∧ ∀ Bstar : ℝ, 0 < Bstar → ∃ w₀ : ℕ, 0 < w₀ ∧
--         ∀ w ≥ w₀, ∀ m : ℕ, (2*A*k)*(m:ℝ) ≤ Bstar →
--         ∀ v : ℕ, 2*cellWidth w m 0 ≤ v →
--         ∀ (a : ℝ) (π : Environment d → LayerTupleProfile (k:=k) e a),
--           @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π →
--         environmentLaw ν (⋃ i, scheduledCellSuccess ν e f hef a C c g₀ g₁ A hc π v w m s i)ᶜ ≤
--           (2:ℝ≥0∞)^(m-1)*ENNReal.ofReal (Real.exp (-2*k*m))
--   ```
--
--   **Definitions.** The statement is written with `OAI.DirectionalTransience.BelowHeight`, `OAI.DirectionalTransience.LayerTupleProfile`, `OAI.DirectionalTransience.TupleAtHeight` and `OAI.DirectionalTransience.rowSigma` (definitions bundle `OAIQ242Bal000` of this split); `OAI.DirectionalTransience.cellWidth` (definitions bundle `OAIQ242Bal001` of this split); `OAI.DirectionalTransience.scheduledCellSuccess` (definitions bundle `OAIQ242Bal007` of this split); `OAI.DirectionalTransience.Direction`, `OAI.DirectionalTransience.DirectionallyTransient`, `OAI.DirectionalTransience.Environment`, `OAI.DirectionalTransience.Lattice`, `OAI.DirectionalTransience.Row`, `OAI.DirectionalTransience.UniformElliptic`, `OAI.DirectionalTransience.environmentLaw`, `OAI.DirectionalTransience.realPosition` and `OAI.DirectionalTransience.step` (the published bundle `Def_DirectionalBallisticity`).
--
--   **Used by.** The proof of `OAI.DirectionalTransience.actual_finite_stage_estimate` of this split imports it.
-- source:
--   OpenAI, Directional transience implies ballisticity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 220; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Estimates/ScheduledCellSuccess.lean (declaration OAI.DirectionalTransience.actual_cell_no_success)

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal007

section

attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualArray_metrizable _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.arrayClassKernel_markov _root_.OAI.DirectionalTransience.coordinateProfile_finite _root_.OAI.DirectionalTransience.currentAnchorKernel_markov _root_.OAI.DirectionalTransience.currentClassKernel_markov _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_compact _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentStoppedProfile_probability _root_.OAI.DirectionalTransience.currentWindowReference_markov _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_compact _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeInputLaw_probability _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalCoordinateKernel_finite _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.instCountableHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSingletonClassHorizontalLayer _root_.OAI.DirectionalTransience.instMeasurableSpaceHorizontalLayer _root_.OAI.DirectionalTransience.properProfileKernel_finite _root_.OAI.DirectionalTransience.rawCurrentOccupation_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

theorem actual_cell_no_success {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ k : ℕ, 2 ≤ k →
      ∃ C c g₀ g₁ : ℝ, 0 < C ∧ ∃ hc : 0 < c, c ≤ 1 ∧ 0 < g₀ ∧ 0 < g₁ ∧
      ∃ s : ℕ, 0 < s ∧ ∀ Bstar : ℝ, 0 < Bstar → ∃ w₀ : ℕ, 0 < w₀ ∧
      ∀ w ≥ w₀, ∀ m : ℕ, (2*A*k)*(m:ℝ) ≤ Bstar →
      ∀ v : ℕ, 2*cellWidth w m 0 ≤ v →
      ∀ (a : ℝ) (π : Environment d → LayerTupleProfile (k:=k) e a),
        @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π →
      environmentLaw ν (⋃ i, scheduledCellSuccess ν e f hef a C c g₀ g₁ A hc π v w m s i)ᶜ ≤
        (2:ℝ≥0∞)^(m-1)*ENNReal.ofReal (Real.exp (-2*k*m)) := by
  sorry

end DirectionalTransience

end

end OAI
end
