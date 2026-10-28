-- Prove2me | Theorems.Thm_OAI_MetricKMedian_Reduction_Serving_bad_count_s35
-- name    : OAI.MetricKMedian.Reduction.Serving.bad_count_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T10:37:58.418163+00:00
-- url     : https://prove2.me/theorems/607e3f16-b22e-4fc5-a0a7-74e8b6675750
-- title:
--   OAI.MetricKMedian.Reduction.Serving.bad_count_s35: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.Reduction.Serving`, with `open Finset`):
--
--   ```lean
--   theorem bad_count_s35 (D : Serving (I:=I) U) (hUF : U ⊆ F)
--       (α δ η : ℝ) (c : ℕ) (hc : 0 < c) (hδ : 0 < δ) (hη : 0 < η)
--       (hC : 0 < cost I O) (hcost : cost I U ≤ α*cost I O)
--       (hsp : Sparse (I:=I) F O (δ*η/(2*c)))
--       (hstuck : ∀ t : ↥U, η*cost I O/c ≤ cost I (U.erase t.val)-cost I U) :
--       ((D.bad O δ).card:ℝ) ≤ 6*α*c/(δ*η)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Reduction.Serving`, `OAI.MetricKMedian.Reduction.Sparse` and `OAI.MetricKMedian.Reduction.Serving.bad` (definitions bundle `OAIQ035K026` of this split); `OAI.MetricKMedian.Instance` and `OAI.MetricKMedian.cost` (the published bundle `Def_MetricKMedian`).
--
--   **Used by.** The proof of `OAI.MetricKMedian.Reduction.completion_branch_exists_s35` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_OAIQ035K026

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

variable {I : Instance}

namespace Serving
variable {U F O : Finset (Fin I.n)}

theorem bad_count_s35 (D : Serving (I:=I) U) (hUF : U ⊆ F)
    (α δ η : ℝ) (c : ℕ) (hc : 0 < c) (hδ : 0 < δ) (hη : 0 < η)
    (hC : 0 < cost I O) (hcost : cost I U ≤ α*cost I O)
    (hsp : Sparse (I:=I) F O (δ*η/(2*c)))
    (hstuck : ∀ t : ↥U, η*cost I O/c ≤ cost I (U.erase t.val)-cost I U) :
    ((D.bad O δ).card:ℝ) ≤ 6*α*c/(δ*η) := by
  sorry

end Serving
end MetricKMedian.Reduction
end
end

end OAI
end
