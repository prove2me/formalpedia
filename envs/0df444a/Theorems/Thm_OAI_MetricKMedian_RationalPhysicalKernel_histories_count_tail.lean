-- Prove2me | Theorems.Thm_OAI_MetricKMedian_RationalPhysicalKernel_histories_count_tail
-- name    : OAI.MetricKMedian.RationalPhysicalKernel.histories_count_tail
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-27T08:35:46.51715+00:00
-- url     : https://prove2.me/theorems/5b2b1339-34a8-4084-8242-541ac14c8365
-- title:
--   OAI.MetricKMedian.RationalPhysicalKernel.histories_count_tail: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.RationalPhysicalKernel`, with `open Finset PhysicalPotential`):
--
--   ```lean
--   theorem histories_count_tail (d : F → F → ℚ) (location : F → X)
--       (hd : ∀ i j, dist (location i) (location j)=(d i j:ℝ))
--       (g β p φ : ℚ) (P : ℕ → ℚ)
--       (hp0 : 0 ≤ p) (hφ0 : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
--       (A : Finset (CopyState.Copy (F := F) Δ)) (T : ℕ)
--       (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ) ≤ 1) (hp : 0 < (p:ℝ))
--       (hφ : 0 < (φ:ℝ)) (hφ1 : (φ:ℝ) ≤ 1) (hβ : 0 < (β:ℝ))
--       (hunit : (g:ℝ)*(Δ:ℝ)=1)
--       (hP : ∀ t < T, 0 < (P t:ℝ)) (hP1 : ∀ t < T, (P t:ℝ) ≤ 1/2)
--       (hA : 1 ≤ mass (g:ℝ) A) (hsmall : 8*(p:ℝ)*(Δ:ℝ) ≤ (φ:ℝ)*(g:ℝ)) :
--       (histories d g β p φ P hp0 hφ0 hupper A T).expectation
--         (fun z => if mass (g:ℝ) A+(T:ℝ)*(4/((g:ℝ)*(β:ℝ))) < mass (g:ℝ) z.1.1 then 1 else 0) ≤
--         (T:ℝ)*(96*(Δ:ℝ)^2*(β:ℝ)/((p:ℝ)*(φ:ℝ)^2*(g:ℝ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.CopyState.Copy` and `OAI.MetricKMedian.PhysicalPotential.mass` (definitions bundle `OAIQ035K003` of this split); `OAI.MetricKMedian.SparseHistories.History` (definitions bundle `OAIQ035K005` of this split); `OAI.MetricKMedian.RationalPhysicalKernel.Payload` and `OAI.MetricKMedian.RationalPhysicalKernel.State` (definitions bundle `OAIQ035K017` of this split); `OAI.MetricKMedian.SparseIntegerLaw.expectation` (definitions bundle `OAIQ035K045` of this split); `OAI.MetricKMedian.RationalPhysicalKernel.histories` (definitions bundle `OAIQ035K047` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.FixedBatch.RationalParameters.selectCompleted_spec` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K045
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
variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {Δ : ℕ}

omit [Fintype F] in

theorem histories_count_tail (d : F → F → ℚ) (location : F → X)
    (hd : ∀ i j, dist (location i) (location j)=(d i j:ℝ))
    (g β p φ : ℚ) (P : ℕ → ℚ)
    (hp0 : 0 ≤ p) (hφ0 : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (A : Finset (CopyState.Copy (F := F) Δ)) (T : ℕ)
    (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ) ≤ 1) (hp : 0 < (p:ℝ))
    (hφ : 0 < (φ:ℝ)) (hφ1 : (φ:ℝ) ≤ 1) (hβ : 0 < (β:ℝ))
    (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : ∀ t < T, 0 < (P t:ℝ)) (hP1 : ∀ t < T, (P t:ℝ) ≤ 1/2)
    (hA : 1 ≤ mass (g:ℝ) A) (hsmall : 8*(p:ℝ)*(Δ:ℝ) ≤ (φ:ℝ)*(g:ℝ)) :
    (histories d g β p φ P hp0 hφ0 hupper A T).expectation
      (fun z => if mass (g:ℝ) A+(T:ℝ)*(4/((g:ℝ)*(β:ℝ))) < mass (g:ℝ) z.1.1 then 1 else 0) ≤
      (T:ℝ)*(96*(Δ:ℝ)^2*(β:ℝ)/((p:ℝ)*(φ:ℝ)^2*(g:ℝ))) := by
  sorry

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
end
