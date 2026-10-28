-- Prove2me | Theorems.Thm_OAI_MetricKMedian_SparseHistories_history_contraction
-- name    : OAI.MetricKMedian.SparseHistories.history_contraction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:33:48.450045+00:00
-- url     : https://prove2.me/theorems/0ecca083-246e-44fa-94cb-633d6b4b8f84
-- title:
--   OAI.MetricKMedian.SparseHistories.history_contraction: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.SparseHistories`, with `open Finset`):
--
--   ```lean
--   theorem history_contraction (κ : ℕ → α → SparseIntegerLaw α) (a : α)
--       (V : ℕ → History α → ℝ) (r : ℝ) (hr : 0 ≤ r) (T : ℕ)
--       (hstep : ∀ t < T, ∀ i : Fin (tree κ a t).length,
--         (κ t (tree κ a t).states[i.val].1).expectation
--           (fun s => V (t+1) (extend (tree κ a t).states[i.val] s)) ≤
--             r*V t (tree κ a t).states[i.val]) :
--       (tree κ a T).expectation (V T) ≤ r^T*V 0 (a,[])
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.SparseHistories.History` (definitions bundle `OAIQ035K005` of this split); `OAI.MetricKMedian.SparseIntegerLaw` (definitions bundle `OAIQ035K017` of this split); `OAI.MetricKMedian.SparseHistories.extend` (definitions bundle `OAIQ035K019` of this split); `OAI.MetricKMedian.SparseHistories.tree` (definitions bundle `OAIQ035K040` of this split); `OAI.MetricKMedian.SparseIntegerLaw.expectation` (definitions bundle `OAIQ035K045` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.RationalPhysicalKernel.histories_survival` of this split imports it.
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

theorem history_contraction (κ : ℕ → α → SparseIntegerLaw α) (a : α)
    (V : ℕ → History α → ℝ) (r : ℝ) (hr : 0 ≤ r) (T : ℕ)
    (hstep : ∀ t < T, ∀ i : Fin (tree κ a t).length,
      (κ t (tree κ a t).states[i.val].1).expectation
        (fun s => V (t+1) (extend (tree κ a t).states[i.val] s)) ≤
          r*V t (tree κ a t).states[i.val]) :
    (tree κ a T).expectation (V T) ≤ r^T*V 0 (a,[]) := by
  sorry

end MetricKMedian.SparseHistories
end
end

end OAI
end
