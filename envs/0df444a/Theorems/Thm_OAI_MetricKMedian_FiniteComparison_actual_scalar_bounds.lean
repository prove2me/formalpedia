-- Prove2me | Theorems.Thm_OAI_MetricKMedian_FiniteComparison_actual_scalar_bounds
-- name    : OAI.MetricKMedian.FiniteComparison.actual_scalar_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:26:29.098249+00:00
-- url     : https://prove2.me/theorems/6b6244cd-0b74-4793-bc31-be8c394d6d1c
-- title:
--   OAI.MetricKMedian.FiniteComparison.actual_scalar_bounds: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.FiniteComparison`, with `open Analytic`):
--
--   ```lean
--   theorem actual_scalar_bounds {x w : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1)
--       (hw0 : 0 ≤ w) (hw : w ≤ 1-x) :
--       ScalarBounds (P x) (m x) (A x+2*P x*w) (P x*w^2) (Certificates.h (1-x)) (actualB x w)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Analytic.A`, `OAI.MetricKMedian.Analytic.P` and `OAI.MetricKMedian.Analytic.m` (definitions bundle `OAIQ035K000` of this split); `OAI.MetricKMedian.Certificates.h` (definitions bundle `OAIQ035K002` of this split); `OAI.MetricKMedian.FiniteComparison.actualB` (definitions bundle `OAIQ035K016` of this split); `OAI.MetricKMedian.FiniteComparison.ScalarBounds` (definitions bundle `OAIQ035K029` of this split).
--
--   **Used by.** The proofs of `OAI_MetricKMedian_GraphComparison_uniform_drift_le` and `OAI.MetricKMedian.GraphComparison.unnormalized_drift_le` of this split import it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K029

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteComparison

open Analytic

theorem actual_scalar_bounds {x w : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1)
    (hw0 : 0 ≤ w) (hw : w ≤ 1-x) :
    ScalarBounds (P x) (m x) (A x+2*P x*w) (P x*w^2) (Certificates.h (1-x)) (actualB x w) := by
  sorry

end MetricKMedian.FiniteComparison

end
end

end OAI
end
