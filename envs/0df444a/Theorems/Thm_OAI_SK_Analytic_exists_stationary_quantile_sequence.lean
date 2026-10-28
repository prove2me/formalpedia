-- Prove2me | Theorems.Thm_OAI_SK_Analytic_exists_stationary_quantile_sequence
-- name    : OAI.SK.Analytic.exists_stationary_quantile_sequence
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T04:57:17.295636+00:00
-- url     : https://prove2.me/theorems/9e548e55-b7b2-4b35-b448-f6b5789127dc
-- title:
--   OAI.SK.Analytic.exists_stationary_quantile_sequence: intermediate lemma from OpenAI, Stretched-exponential barriers for typical SK initial states
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SK.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Stretched-exponential barriers for typical SK initial states*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SK.Analytic.exists_stationary_quantile_sequence` of [lean/OAI/Probability/SKBarriers/SKBarriers/Scalar/StationaryApproximation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Scalar/StationaryApproximation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SK.Analytic`, with `open scoped BigOperators Topology`, `open MeasureTheory ProbabilityTheory Filter`):
--
--   ```lean
--   theorem exists_stationary_quantile_sequence (β : ℝ) :
--       ∃ K : ℕ → ℕ, ∃ A : (n : ℕ) → Fin (K n+1) → ℝ,
--         (∀ n, A n ∈ admissibleQuantiles (K n)) ∧
--         (∀ n B, B ∈ admissibleQuantiles (K n) →
--           extendedQuantileParisi (K n) β (A n) ≤ extendedQuantileParisi (K n) β B) ∧
--         (∀ n B, B ∈ admissibleQuantiles (K n) → 0 ≤ (β^2/2)*∑ j : Fin (K n+1),
--           ((K n+1:ℕ):ℝ)⁻¹*(B j-A n j)*(A n j-quantileOverlapMean (K n) β (A n) j)) ∧
--         Tendsto (fun n => extendedQuantileParisi (K n) β (A n)) atTop (𝓝 (finiteParisiInf β))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SK.Analytic.admissibleQuantiles` (definitions bundle `OAIQ036S001` of this split); `OAI.SK.Analytic.extendedQuantileParisi`, `OAI.SK.Analytic.finiteParisiInf` and `OAI.SK.Analytic.quantileOverlapMean` (definitions bundle `OAIQ036S004` of this split).
--
--   **Used by.** The proof of `OAI.SK.Analytic.exists_scalarCDFParisi_minimizer_locking_data` of this split imports it.
-- source:
--   OpenAI, Stretched-exponential barriers for typical SK initial states, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Stretched-exponential-barriers-for-typical-SK-initial-states-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKBarriers/SKBarriers/Scalar/StationaryApproximation.lean (declaration OAI.SK.Analytic.exists_stationary_quantile_sequence)

import Mathlib
import Definitions.Def_OAIQ036S004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic

theorem exists_stationary_quantile_sequence (β : ℝ) :
    ∃ K : ℕ → ℕ, ∃ A : (n : ℕ) → Fin (K n+1) → ℝ,
      (∀ n, A n ∈ admissibleQuantiles (K n)) ∧
      (∀ n B, B ∈ admissibleQuantiles (K n) →
        extendedQuantileParisi (K n) β (A n) ≤ extendedQuantileParisi (K n) β B) ∧
      (∀ n B, B ∈ admissibleQuantiles (K n) → 0 ≤ (β^2/2)*∑ j : Fin (K n+1),
        ((K n+1:ℕ):ℝ)⁻¹*(B j-A n j)*(A n j-quantileOverlapMean (K n) β (A n) j)) ∧
      Tendsto (fun n => extendedQuantileParisi (K n) β (A n)) atTop (𝓝 (finiteParisiInf β)) := by
  sorry

end SK.Analytic

end
end

end

end OAI
end
