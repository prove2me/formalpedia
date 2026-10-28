-- Prove2me | Theorems.Thm_OAI_MetricKMedian_RationalPhysicalKernel_histories_mass
-- name    : OAI.MetricKMedian.RationalPhysicalKernel.histories_mass
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:35:47.195723+00:00
-- url     : https://prove2.me/theorems/d2a849e1-a2f9-4d4f-8acc-068e1c417ab8
-- title:
--   OAI.MetricKMedian.RationalPhysicalKernel.histories_mass: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.RationalPhysicalKernel`, with `open Finset PhysicalPotential`):
--
--   ```lean
--   theorem histories_mass (d : F → F → ℚ) (g β p φ : ℚ) (P : ℕ → ℚ)
--       (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
--       (A : Finset (CopyState.Copy (F := F) Δ)) (T : ℕ)
--       (hg : 0 ≤ (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1) (hA : 1 ≤ mass (g:ℝ) A)
--       (i : Fin (histories d g β p φ P hp hφ hupper A T).length) :
--       1 ≤ mass (g:ℝ) (histories d g β p φ P hp hφ hupper A T).states[i.val].1.1
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.CopyState.Copy` and `OAI.MetricKMedian.PhysicalPotential.mass` (definitions bundle `OAIQ035K003` of this split); `OAI.MetricKMedian.SparseHistories.History` (definitions bundle `OAIQ035K005` of this split); `OAI.MetricKMedian.RationalPhysicalKernel.Payload`, `OAI.MetricKMedian.RationalPhysicalKernel.State` and `OAI.MetricKMedian.SparseIntegerLaw` (definitions bundle `OAIQ035K017` of this split); `OAI.MetricKMedian.RationalPhysicalKernel.histories` (definitions bundle `OAIQ035K047` of this split).
--
--   **Used by.** The proofs of `OAI_MetricKMedian_RationalPhysicalKernel_histories_completed_expectation`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_count_tail`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_drift` and `OAI.MetricKMedian.RationalPhysicalKernel.histories_survival` of this split import it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K047

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset PhysicalPotential
variable {F : Type} [LinearOrder F] [Fintype F] {Δ : ℕ}

omit [Fintype F] in

theorem histories_mass (d : F → F → ℚ) (g β p φ : ℚ) (P : ℕ → ℚ)
    (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (A : Finset (CopyState.Copy (F := F) Δ)) (T : ℕ)
    (hg : 0 ≤ (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1) (hA : 1 ≤ mass (g:ℝ) A)
    (i : Fin (histories d g β p φ P hp hφ hupper A T).length) :
    1 ≤ mass (g:ℝ) (histories d g β p φ P hp hφ hupper A T).states[i.val].1.1 := by
  sorry

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
end
