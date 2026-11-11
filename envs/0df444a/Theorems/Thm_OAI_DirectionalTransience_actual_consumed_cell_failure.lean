-- Prove2me | Theorems.Thm_OAI_DirectionalTransience_actual_consumed_cell_failure
-- name    : OAI.DirectionalTransience.actual_consumed_cell_failure
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:51:52.230201+00:00
-- url     : https://prove2.me/theorems/7cecfbe1-fde5-4e1d-bd3b-5fe710c59828
-- title:
--   OAI.DirectionalTransience.actual_consumed_cell_failure: intermediate lemma from OpenAI, Directional transience implies ballisticity
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectionalTransience.directional_transience_implies_ballisticity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Directional transience implies ballisticity*, OpenAI Math Release, September 23, 2026, result family 220, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DirectionalTransience.actual_consumed_cell_failure` of [lean/OAI/Probability/Ballisticity/Estimates/Cell.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Estimates/Cell.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DirectionalTransience`, with `open MeasureTheory ProbabilityTheory`, `open scoped ENNReal BigOperators Classical`):
--
--   ```lean
--   theorem actual_consumed_cell_failure {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
--       (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
--       (htrans : DirectionallyTransient ν (realPosition (step e))) :
--       ∃ A : ℝ, 1 ≤ A ∧ ∀ k : ℕ, 2 ≤ k →
--         ∃ C c g₀ g₁ : ℝ, 0 < C ∧ ∃ hc : 0 < c, c ≤ 1 ∧ 0 < g₀ ∧ 0 < g₁ ∧
--         ∃ s H₀ : ℕ, 0 < s ∧ ∀ Bstar : ℝ, 0 < Bstar → ∃ R : ℝ, 0 < R ∧
--         ∀ Hs ≥ H₀, ∀ (ρ : ℝ) (hρ : 0 < ρ), R ≤ ρ →
--           ρ = fluctuationRadius (independentConditionedPairLaw ν (realPosition (step e)))
--             (commonIncrementProcess (realPosition (step e)) f 0) ((Hs:ℝ)/C) →
--         ∀ He : ℕ, (He:ℝ) ≤ 3*C*fluctuationScale
--           (independentConditionedPairLaw ν (realPosition (step e)))
--           (commonIncrementProcess (realPosition (step e)) f 0) ρ →
--         ∀ H : ℕ → ℕ, (∀ i, (H i:ℝ) ≤ 3*C*fluctuationScale
--           (independentConditionedPairLaw ν (realPosition (step e)))
--           (commonIncrementProcess (realPosition (step e)) f 0) ρ/(16:ℝ)^(s+i)) →
--         ∀ m : ℕ, (2*A*k)*m ≤ Bstar → ∀ n : ℕ, 1 ≤ n → n ≤ m →
--         ∀ (a : ℝ) (π : Environment d → LayerTupleProfile (k:=k) e a),
--           @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π →
--         ∀ E : Set (Environment d), MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) a)] E →
--           environmentLaw ν (E∩consumedCellFailure
--             (cellSeedMass e f a (c*ρ) Hs π) (cellEarlyMass e f hef a (c*ρ) Hs He π)
--             (cellLateMass e f hef a c ρ hc hρ Hs He s H π) g₀ g₁ (A*k) s m n) ≤
--               ENNReal.ofReal (Real.exp (-2*k*n))*environmentLaw ν E
--   ```
--
--   **Definitions.** The statement is written with `OAI.DirectionalTransience.BelowHeight`, `OAI.DirectionalTransience.LayerTupleProfile`, `OAI.DirectionalTransience.TupleAtHeight`, `OAI.DirectionalTransience.commonIncrementProcess`, `OAI.DirectionalTransience.fluctuationScale`, `OAI.DirectionalTransience.independentConditionedPairLaw` and `OAI.DirectionalTransience.rowSigma` (definitions bundle `OAIQ242Bal000` of this split); `OAI.DirectionalTransience.consumedCellFailure` (definitions bundle `OAIQ242Bal001` of this split); `OAI.DirectionalTransience.fluctuationRadius` (definitions bundle `OAIQ242Bal002` of this split); `OAI.DirectionalTransience.cellEarlyMass`, `OAI.DirectionalTransience.cellLateMass` and `OAI.DirectionalTransience.cellSeedMass` (definitions bundle `OAIQ242Bal003` of this split); `OAI.DirectionalTransience.Direction`, `OAI.DirectionalTransience.DirectionallyTransient`, `OAI.DirectionalTransience.Environment`, `OAI.DirectionalTransience.Lattice`, `OAI.DirectionalTransience.Path`, `OAI.DirectionalTransience.Row`, `OAI.DirectionalTransience.UniformElliptic`, `OAI.DirectionalTransience.environmentLaw`, `OAI.DirectionalTransience.realPosition` and `OAI.DirectionalTransience.step` (the published bundle `Def_DirectionalBallisticity`).
--
--   **Used by.** The proof of `OAI.DirectionalTransience.actual_cell_no_success` of this split imports it.
-- source:
--   OpenAI, Directional transience implies ballisticity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 220; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Estimates/Cell.lean (declaration OAI.DirectionalTransience.actual_consumed_cell_failure)

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal002
import Definitions.Def_OAIQ242Bal003

section

attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.actualOccupationRaw_finite _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.episodeAuxiliaryLaw_probability _root_.OAI.DirectionalTransience.episodeInputLaw_finite _root_.OAI.DirectionalTransience.episodeProfile_probability _root_.OAI.DirectionalTransience.globalEndpointProfile_probability _root_.OAI.DirectionalTransience.globalEpisodeAnchors_markov _root_.OAI.DirectionalTransience.globalHorizontalProfile_probability _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

theorem actual_consumed_cell_failure {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1 ≠ f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ k : ℕ, 2 ≤ k →
      ∃ C c g₀ g₁ : ℝ, 0 < C ∧ ∃ hc : 0 < c, c ≤ 1 ∧ 0 < g₀ ∧ 0 < g₁ ∧
      ∃ s H₀ : ℕ, 0 < s ∧ ∀ Bstar : ℝ, 0 < Bstar → ∃ R : ℝ, 0 < R ∧
      ∀ Hs ≥ H₀, ∀ (ρ : ℝ) (hρ : 0 < ρ), R ≤ ρ →
        ρ = fluctuationRadius (independentConditionedPairLaw ν (realPosition (step e)))
          (commonIncrementProcess (realPosition (step e)) f 0) ((Hs:ℝ)/C) →
      ∀ He : ℕ, (He:ℝ) ≤ 3*C*fluctuationScale
        (independentConditionedPairLaw ν (realPosition (step e)))
        (commonIncrementProcess (realPosition (step e)) f 0) ρ →
      ∀ H : ℕ → ℕ, (∀ i, (H i:ℝ) ≤ 3*C*fluctuationScale
        (independentConditionedPairLaw ν (realPosition (step e)))
        (commonIncrementProcess (realPosition (step e)) f 0) ρ/(16:ℝ)^(s+i)) →
      ∀ m : ℕ, (2*A*k)*m ≤ Bstar → ∀ n : ℕ, 1 ≤ n → n ≤ m →
      ∀ (a : ℝ) (π : Environment d → LayerTupleProfile (k:=k) e a),
        @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) a)) _ π →
      ∀ E : Set (Environment d), MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) a)] E →
        environmentLaw ν (E∩consumedCellFailure
          (cellSeedMass e f a (c*ρ) Hs π) (cellEarlyMass e f hef a (c*ρ) Hs He π)
          (cellLateMass e f hef a c ρ hc hρ Hs He s H π) g₀ g₁ (A*k) s m n) ≤
            ENNReal.ofReal (Real.exp (-2*k*n))*environmentLaw ν E := by
  sorry

end DirectionalTransience

end

end OAI
end
