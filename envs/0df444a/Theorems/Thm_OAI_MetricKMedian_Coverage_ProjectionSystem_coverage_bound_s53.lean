-- Prove2me | Theorems.Thm_OAI_MetricKMedian_Coverage_ProjectionSystem_coverage_bound_s53
-- name    : OAI.MetricKMedian.Coverage.ProjectionSystem.coverage_bound_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:31:32.524064+00:00
-- url     : https://prove2.me/theorems/84606245-83dd-445d-aa94-529e2ff46f04
-- title:
--   OAI.MetricKMedian.Coverage.ProjectionSystem.coverage_bound_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.Coverage.ProjectionSystem.coverage_bound` of [lean/OAI/Combinatorics/KMedian/Hardness/Projection.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Hardness/Projection.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.Coverage.ProjectionSystem`, with `open Finset`):
--
--   ```lean
--   theorem coverage_bound_s53 {d : ℕ} (hreg : G.LeftRegular d)
--       (hI : 1 < Fintype.card I) (S : Finset (U × A)) (hS : S.card ≤ Fintype.card U) :
--       ((G.covered S).card:ℝ) ≤ (Fintype.card I:ℝ)^Fintype.card B *
--         ((Fintype.card V:ℝ)*(1-(1-1/(Fintype.card I:ℝ))^Fintype.card I)+(G.bad S).card)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Coverage.ProjectionSystem`, `OAI.MetricKMedian.Coverage.ProjectionSystem.LeftRegular`, `OAI.MetricKMedian.Coverage.ProjectionSystem.bad` and `OAI.MetricKMedian.Coverage.ProjectionSystem.covered` (definitions bundle `OAIQ053K006` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.Coverage.ProjectionSystem.coverage_agreement_bound_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Hardness/Projection.lean (declaration OAI.MetricKMedian.Coverage.ProjectionSystem.coverage_bound)

import Mathlib
import Definitions.Def_OAIQ053K006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage
open Finset

namespace ProjectionSystem
variable {U V I A B : Type} [Fintype U] [Fintype V] [Fintype I]
  [Fintype A] [Fintype B] [DecidableEq U] [DecidableEq V] [DecidableEq I]
  [DecidableEq A] [DecidableEq B]
variable (G : ProjectionSystem U V I A B)

theorem coverage_bound_s53 {d : ℕ} (hreg : G.LeftRegular d)
    (hI : 1 < Fintype.card I) (S : Finset (U × A)) (hS : S.card ≤ Fintype.card U) :
    ((G.covered S).card:ℝ) ≤ (Fintype.card I:ℝ)^Fintype.card B *
      ((Fintype.card V:ℝ)*(1-(1-1/(Fintype.card I:ℝ))^Fintype.card I)+(G.bad S).card) := by
  sorry

end ProjectionSystem
end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI
end
