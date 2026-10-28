-- Prove2me | Theorems.Thm_OAI_MetricKMedian_SparseHistories_count_tail_up_to_s35
-- name    : OAI.MetricKMedian.SparseHistories.count_tail_up_to_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T10:45:01.031922+00:00
-- url     : https://prove2.me/theorems/39a26eec-9f8a-4ce7-bd82-d8a837c9baf7
-- title:
--   OAI.MetricKMedian.SparseHistories.count_tail_up_to_s35: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.SparseHistories`, with `open Finset`):
--
--   ```lean
--   theorem count_tail_up_to_s35 (κ : ℕ → α → SparseIntegerLaw α) (a : α)
--       (size : α → ℝ) (c ρ : ℝ)
--       (T : ℕ)
--       (hstep : ∀ t < T, ∀ i : ℕ, ∀ hi : i < (tree κ a t).length,
--         (κ t (tree κ a t).states[i].1).expectation
--           (fun s => if size (tree κ a t).states[i].1+c < size s then 1 else 0) ≤ ρ)
--       :
--       (tree κ a T).expectation (fun h => if size a+(T:ℝ)*c < size h.1 then 1 else 0) ≤
--         (T:ℝ)*ρ
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.SparseHistories.History` (definitions bundle `OAIQ035K005` of this split); `OAI.MetricKMedian.SparseIntegerLaw` (definitions bundle `OAIQ035K017` of this split); `OAI.MetricKMedian.SparseHistories.tree` (definitions bundle `OAIQ035K040` of this split); `OAI.MetricKMedian.SparseIntegerLaw.expectation` (definitions bundle `OAIQ035K045` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.RationalPhysicalKernel.histories_count_tail_s35` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K040
import Definitions.Def_OAIQ035K045

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseHistories
open Finset
variable {α : Type}

theorem count_tail_up_to_s35 (κ : ℕ → α → SparseIntegerLaw α) (a : α)
    (size : α → ℝ) (c ρ : ℝ)
    (T : ℕ)
    (hstep : ∀ t < T, ∀ i : ℕ, ∀ hi : i < (tree κ a t).length,
      (κ t (tree κ a t).states[i].1).expectation
        (fun s => if size (tree κ a t).states[i].1+c < size s then 1 else 0) ≤ ρ)
    :
    (tree κ a T).expectation (fun h => if size a+(T:ℝ)*c < size h.1 then 1 else 0) ≤
      (T:ℝ)*ρ := by
  sorry

end MetricKMedian.SparseHistories
end
end

end OAI
end
