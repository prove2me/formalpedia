-- Prove2me | Theorems.Thm_OAI_MetricKMedian_Reduction_sparse_branch_exists_s35
-- name    : OAI.MetricKMedian.Reduction.sparse_branch_exists_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T10:40:19.963527+00:00
-- url     : https://prove2.me/theorems/89937960-0ca1-43fe-9733-205668a5d649
-- title:
--   OAI.MetricKMedian.Reduction.sparse_branch_exists_s35: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.Reduction`, with `open Finset`):
--
--   ```lean
--   theorem sparse_branch_exists_s35 (F O : Finset (Fin I.n)) (hOF : O ⊆ F) (hO : O.Nonempty)
--       (hcost : 0 < cost I O) (ρ : ℝ) (hρ : 0 < ρ) (b : ℕ) (hb : (3/2:ℝ) ≤ b*ρ) :
--       ∃ F' ∈ sparseBranches I F b, O ⊆ F' ∧ Sparse (I:=I) F' O ρ
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Reduction.Sparse` (definitions bundle `OAIQ035K026` of this split); `OAI.MetricKMedian.Reduction.sparseBranches` (definitions bundle `OAIQ035K036` of this split); `OAI.MetricKMedian.Instance` and `OAI.MetricKMedian.cost` (the published bundle `Def_MetricKMedian`).
--
--   **Used by.** The proof of `OAI.MetricKMedian.Reduction.Program.ordinarySet_spec_s35` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_OAIQ035K036

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

theorem sparse_branch_exists_s35 (F O : Finset (Fin I.n)) (hOF : O ⊆ F) (hO : O.Nonempty)
    (hcost : 0 < cost I O) (ρ : ℝ) (hρ : 0 < ρ) (b : ℕ) (hb : (3/2:ℝ) ≤ b*ρ) :
    ∃ F' ∈ sparseBranches I F b, O ⊆ F' ∧ Sparse (I:=I) F' O ρ := by
  sorry

end MetricKMedian.Reduction
end
end

end OAI
end
