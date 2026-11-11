-- Prove2me | Theorems.Thm_OAI_DirectionalTransience_actual_late_protection_first_failure
-- name    : OAI.DirectionalTransience.actual_late_protection_first_failure
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:48:57.852546+00:00
-- url     : https://prove2.me/theorems/90fe6202-656e-4174-abf9-d65029723330
-- title:
--   OAI.DirectionalTransience.actual_late_protection_first_failure: intermediate lemma from OpenAI, Directional transience implies ballisticity
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectionalTransience.directional_transience_implies_ballisticity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Directional transience implies ballisticity*, OpenAI Math Release, September 23, 2026, result family 220, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DirectionalTransience.actual_late_protection_first_failure` of [lean/OAI/Probability/Ballisticity/Estimates/ProtectionFirstFailure.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Estimates/ProtectionFirstFailure.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DirectionalTransience`, with `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal BigOperators Classical`):
--
--   ```lean
--   theorem actual_late_protection_first_failure {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
--       (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1≠f.1)
--       (htrans : DirectionallyTransient ν (realPosition (step e))) :
--       ∃ lam Cmg : ℝ, 0<lam ∧ lam≤1 ∧ 0<Cmg ∧
--         ∀ A : ℝ, 1≤A → Cmg+8≤(lam/4)*A → ∀ k : ℕ, 2≤k →
--         ∀ (c C : ℝ) (hc : 0 < c), c≤1 → 0<C → ∃ l₀ : ℕ, 0<l₀ ∧
--         ∀ Bstar : ℝ, 0<Bstar → ∃ R : ℝ, ∃ hR : 0<R,
--         ∀ (ρ : ℝ) (hρR : R≤ρ), ∀ n : ℕ, (2*A*k)*(l₀+n+1)≤Bstar →
--         ∀ H : ℕ → ℕ, (∀ i≤n, (H i:ℝ)≤3*C*fluctuationScale
--           (independentConditionedPairLaw ν (realPosition (step e)))
--           (commonIncrementProcess (realPosition (step e)) f 0) ρ/(16:ℝ)^(l₀+i)) →
--         ∀ base : ℝ, ∀ π : Environment d → BudgetProfile (k:=k) e f base (3*c*ρ/4),
--         @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) base)) _ π →
--         ∀ E : Set (Environment d), MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) base)] E →
--           environmentLaw ν (E∩firstProtectionFailure
--             (protectionMass e f base (3*c*ρ/4) H (lateBudget c ρ l₀)
--               (fun i => (lateBudget_pos hc (lt_of_lt_of_le hR hρR) l₀ i).le) π)
--             (A*k) l₀ n)≤ENNReal.ofReal (Real.exp (-5*k*((l₀:ℝ)+n+1)))*environmentLaw ν E
--   ```
--
--   **Definitions.** The statement is written with `OAI.DirectionalTransience.BelowHeight`, `OAI.DirectionalTransience.BudgetProfile`, `OAI.DirectionalTransience.TupleAtHeight`, `OAI.DirectionalTransience.TupleSeparated`, `OAI.DirectionalTransience.commonIncrementProcess`, `OAI.DirectionalTransience.fluctuationScale`, `OAI.DirectionalTransience.independentConditionedPairLaw` and `OAI.DirectionalTransience.rowSigma` (definitions bundle `OAIQ242Bal000` of this split); `OAI.DirectionalTransience.firstProtectionFailure`, `OAI.DirectionalTransience.lateBudget` and `OAI.DirectionalTransience.lateBudget_pos` (definitions bundle `OAIQ242Bal001` of this split); `OAI.DirectionalTransience.protectionMass` (definitions bundle `OAIQ242Bal003` of this split); `OAI.DirectionalTransience.Direction`, `OAI.DirectionalTransience.DirectionallyTransient`, `OAI.DirectionalTransience.Environment`, `OAI.DirectionalTransience.Lattice`, `OAI.DirectionalTransience.Path`, `OAI.DirectionalTransience.Row`, `OAI.DirectionalTransience.UniformElliptic`, `OAI.DirectionalTransience.environmentLaw`, `OAI.DirectionalTransience.realPosition` and `OAI.DirectionalTransience.step` (the published bundle `Def_DirectionalBallisticity`).
--
--   **Used by.** The proof of `OAI.DirectionalTransience.actual_consumed_cell_failure` of this split imports it.
-- source:
--   OpenAI, Directional transience implies ballisticity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 220; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Estimates/ProtectionFirstFailure.lean (declaration OAI.DirectionalTransience.actual_late_protection_first_failure)

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal003

section

attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Classical
namespace DirectionalTransience

theorem actual_late_protection_first_failure {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d) (hef : e.1≠f.1)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ lam Cmg : ℝ, 0<lam ∧ lam≤1 ∧ 0<Cmg ∧
      ∀ A : ℝ, 1≤A → Cmg+8≤(lam/4)*A → ∀ k : ℕ, 2≤k →
      ∀ (c C : ℝ) (hc : 0 < c), c≤1 → 0<C → ∃ l₀ : ℕ, 0<l₀ ∧
      ∀ Bstar : ℝ, 0<Bstar → ∃ R : ℝ, ∃ hR : 0<R,
      ∀ (ρ : ℝ) (hρR : R≤ρ), ∀ n : ℕ, (2*A*k)*(l₀+n+1)≤Bstar →
      ∀ H : ℕ → ℕ, (∀ i≤n, (H i:ℝ)≤3*C*fluctuationScale
        (independentConditionedPairLaw ν (realPosition (step e)))
        (commonIncrementProcess (realPosition (step e)) f 0) ρ/(16:ℝ)^(l₀+i)) →
      ∀ base : ℝ, ∀ π : Environment d → BudgetProfile (k:=k) e f base (3*c*ρ/4),
      @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) base)) _ π →
      ∀ E : Set (Environment d), MeasurableSet[rowSigma (BelowHeight (realPosition (step e)) base)] E →
        environmentLaw ν (E∩firstProtectionFailure
          (protectionMass e f base (3*c*ρ/4) H (lateBudget c ρ l₀)
            (fun i => (lateBudget_pos hc (lt_of_lt_of_le hR hρR) l₀ i).le) π)
          (A*k) l₀ n)≤ENNReal.ofReal (Real.exp (-5*k*((l₀:ℝ)+n+1)))*environmentLaw ν E := by
  sorry

end DirectionalTransience

end

end OAI
end
