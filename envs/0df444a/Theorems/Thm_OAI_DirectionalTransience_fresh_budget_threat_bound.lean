-- Prove2me | Theorems.Thm_OAI_DirectionalTransience_fresh_budget_threat_bound
-- name    : OAI.DirectionalTransience.fresh_budget_threat_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:48:36.796197+00:00
-- url     : https://prove2.me/theorems/1cf563be-0d16-46e3-894c-e5fea8ef7a05
-- title:
--   OAI.DirectionalTransience.fresh_budget_threat_bound: intermediate lemma from OpenAI, Directional transience implies ballisticity
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DirectionalTransience.directional_transience_implies_ballisticity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Directional transience implies ballisticity*, OpenAI Math Release, September 23, 2026, result family 220, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DirectionalTransience.fresh_budget_threat_bound` of [lean/OAI/Probability/Ballisticity/Coupling/FreshThreat.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Coupling/FreshThreat.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DirectionalTransience`, with `open MeasureTheory ProbabilityTheory Filter`, `open scoped ENNReal BigOperators Topology Classical`):
--
--   ```lean
--   theorem fresh_budget_threat_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
--       (hue : UniformElliptic ν) (e f : Direction d)
--       (htrans : DirectionallyTransient ν (realPosition (step e))) :
--       ∃ lam C D : ℝ, 0 < lam ∧ lam ≤ 1 ∧ 0 < C ∧ 0 < D ∧
--         ∀ Bstar : ℝ, 0 < Bstar → ∀ k : ℕ, 1 ≤ k → ∃ G : ℕ,
--         ∀ (π : Measure (Fin k → Lattice d)) [IsProbabilityMeasure π],
--           (∀ᵐ x ∂π, Pairwise fun i j => (G : ℤ) ≤ |x i f.1 - x j f.1|) →
--           ∀ (H : ℕ) (z s : ℝ), 0 < z → Real.exp (-Bstar) ≤ s →
--           (environmentLaw ν).real (budgetThreatEvent e f H (2*z) π s) ≤
--             Real.exp (C*k)*s^lam + D*k*H /
--               fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
--                 (commonIncrementProcess (realPosition (step e)) f 0) z / s
--   ```
--
--   **Definitions.** The statement is written with `OAI.DirectionalTransience.commonIncrementProcess`, `OAI.DirectionalTransience.fluctuationScale` and `OAI.DirectionalTransience.independentConditionedPairLaw` (definitions bundle `OAIQ242Bal000` of this split); `OAI.DirectionalTransience.budgetThreatEvent` (definitions bundle `OAIQ242Bal003` of this split); `OAI.DirectionalTransience.Direction`, `OAI.DirectionalTransience.DirectionallyTransient`, `OAI.DirectionalTransience.Environment`, `OAI.DirectionalTransience.Lattice`, `OAI.DirectionalTransience.Path`, `OAI.DirectionalTransience.Row`, `OAI.DirectionalTransience.UniformElliptic`, `OAI.DirectionalTransience.environmentLaw`, `OAI.DirectionalTransience.realPosition` and `OAI.DirectionalTransience.step` (the published bundle `Def_DirectionalBallisticity`).
--
--   **Used by.** The proofs of `OAI.DirectionalTransience.actual_finite_stage_estimate` and `OAI.DirectionalTransience.actual_late_protection_first_failure` of this split import it.
-- source:
--   OpenAI, Directional transience implies ballisticity, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 220; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Directional-transience-implies-ballisticity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Ballisticity/Coupling/FreshThreat.lean (declaration OAI.DirectionalTransience.fresh_budget_threat_bound)

import Mathlib
import Definitions.Def_DirectionalBallisticity
import Definitions.Def_OAIQ242Bal003

section

attribute [-instance] _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_countable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_firstCountable _root_.OAI.DirectionalTransience.StationaryCompact.discreteOnePoint_secondCountable _root_.OAI.DirectionalTransience.actualArray_borel _root_.OAI.DirectionalTransience.actualArray_compact _root_.OAI.DirectionalTransience.ambientCurrentWindow_borel _root_.OAI.DirectionalTransience.budgetEndpointMixture_finite _root_.OAI.DirectionalTransience.budgetProfile_probability _root_.OAI.DirectionalTransience.currentDataProfiles_borel _root_.OAI.DirectionalTransience.currentDataProfiles_opens _root_.OAI.DirectionalTransience.currentDataProfiles_secondCountable _root_.OAI.DirectionalTransience.currentData_secondCountable _root_.OAI.DirectionalTransience.currentFields_compact _root_.OAI.DirectionalTransience.currentFields_secondCountable _root_.OAI.DirectionalTransience.currentOffsets_secondCountable _root_.OAI.DirectionalTransience.currentProfiles_secondCountable _root_.OAI.DirectionalTransience.currentWindow_borel _root_.OAI.DirectionalTransience.currentWindow_opens _root_.OAI.DirectionalTransience.currentWindow_secondCountable _root_.OAI.DirectionalTransience.enat_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_borel _root_.OAI.DirectionalTransience.horizontalOnePoint_measurable _root_.OAI.DirectionalTransience.layerTupleProfile_probability _root_.OAI.DirectionalTransience.rawTupleMixture_finite _root_.OAI.DirectionalTransience.row_compact _root_.OAI.DirectionalTransience.row_standardBorel _root_.OAI.DirectionalTransience.seedHalfRaw_finite _root_.OAI.DirectionalTransience.seedSeparatedRaw_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Topology Classical
namespace DirectionalTransience

theorem fresh_budget_threat_bound {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (e f : Direction d)
    (htrans : DirectionallyTransient ν (realPosition (step e))) :
    ∃ lam C D : ℝ, 0 < lam ∧ lam ≤ 1 ∧ 0 < C ∧ 0 < D ∧
      ∀ Bstar : ℝ, 0 < Bstar → ∀ k : ℕ, 1 ≤ k → ∃ G : ℕ,
      ∀ (π : Measure (Fin k → Lattice d)) [IsProbabilityMeasure π],
        (∀ᵐ x ∂π, Pairwise fun i j => (G : ℤ) ≤ |x i f.1 - x j f.1|) →
        ∀ (H : ℕ) (z s : ℝ), 0 < z → Real.exp (-Bstar) ≤ s →
        (environmentLaw ν).real (budgetThreatEvent e f H (2*z) π s) ≤
          Real.exp (C*k)*s^lam + D*k*H /
            fluctuationScale (independentConditionedPairLaw ν (realPosition (step e)))
              (commonIncrementProcess (realPosition (step e)) f 0) z / s := by
  sorry

end DirectionalTransience

end

end OAI
end
