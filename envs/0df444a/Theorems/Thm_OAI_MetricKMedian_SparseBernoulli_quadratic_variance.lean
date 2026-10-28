-- Prove2me | Theorems.Thm_OAI_MetricKMedian_SparseBernoulli_quadratic_variance
-- name    : OAI.MetricKMedian.SparseBernoulli.quadratic_variance
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:30:54.52705+00:00
-- url     : https://prove2.me/theorems/eb16ab05-a051-4118-9f9d-737a5d37d9c1
-- title:
--   OAI.MetricKMedian.SparseBernoulli.quadratic_variance: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.SparseBernoulli`, with `open Finset`):
--
--   ```lean
--   theorem quadratic_variance {m : ℕ} (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
--       (S : Fin m → Finset (Fin n)) (c : Fin m → ℚ) (hS : ∀ j, (S j).card ≤ 2) :
--       (run (d := 4) p hp n).real.variance (fun q => (polynomial S c q:ℝ))=
--         (reference p hp).variance (fun q => (polynomial S c q:ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.FiniteLaw.variance` (definitions bundle `OAIQ035K004` of this split); `OAI.MetricKMedian.SparseBernoulli.polynomial` and `OAI.MetricKMedian.SparseBernoulli.reference` (definitions bundle `OAIQ035K026` of this split); `OAI.MetricKMedian.SparseIntegerLaw.real` (definitions bundle `OAIQ035K029` of this split); `OAI.MetricKMedian.SparseBernoulli.run` (definitions bundle `OAIQ035K039` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.SparseBernoulli.count_failure` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K026
import Definitions.Def_OAIQ035K039

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseBernoulli
open Finset
variable {n : ℕ}

theorem quadratic_variance {m : ℕ} (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (S : Fin m → Finset (Fin n)) (c : Fin m → ℚ) (hS : ∀ j, (S j).card ≤ 2) :
    (run (d := 4) p hp n).real.variance (fun q => (polynomial S c q:ℝ))=
      (reference p hp).variance (fun q => (polynomial S c q:ℝ)) := by
  sorry

end MetricKMedian.SparseBernoulli

end OAI
end
