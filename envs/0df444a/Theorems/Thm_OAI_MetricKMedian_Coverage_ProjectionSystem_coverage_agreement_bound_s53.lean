-- Prove2me | Theorems.Thm_OAI_MetricKMedian_Coverage_ProjectionSystem_coverage_agreement_bound_s53
-- name    : OAI.MetricKMedian.Coverage.ProjectionSystem.coverage_agreement_bound_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:31:02.406026+00:00
-- url     : https://prove2.me/theorems/66b2494f-606a-4b3c-bd58-7426af6cd7e3
-- title:
--   OAI.MetricKMedian.Coverage.ProjectionSystem.coverage_agreement_bound_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.Coverage.ProjectionSystem.coverage_agreement_bound` of [lean/OAI/Combinatorics/KMedian/Hardness/Lists.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Hardness/Lists.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.Coverage.ProjectionSystem`, with `open Finset`):
--
--   ```lean
--   theorem coverage_agreement_bound_s53 {d : ℕ} (hreg : G.LeftRegular d)
--       (hI : 1 < Fintype.card I) (hdup : G.DuplicateConsistent)
--       (S : Finset (U × A)) (hS : S.card ≤ Fintype.card U)
--       {t : ℕ} (ht : 1 ≤ t) (default : A)
--       (γ : ℝ) (hsound : ∀ left, ((G.agreement left).card:ℝ) ≤ γ*Fintype.card V) :
--       ((G.covered S).card:ℝ) ≤
--         (1-(1-1/(Fintype.card I:ℝ))^Fintype.card I+
--           (Fintype.card I:ℝ)/t+(t:ℝ)^2*γ) *
--           ((Fintype.card V:ℝ)*(Fintype.card I:ℝ)^Fintype.card B)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Coverage.ProjectionSystem`, `OAI.MetricKMedian.Coverage.ProjectionSystem.DuplicateConsistent`, `OAI.MetricKMedian.Coverage.ProjectionSystem.LeftRegular`, `OAI.MetricKMedian.Coverage.ProjectionSystem.agreement` and `OAI.MetricKMedian.Coverage.ProjectionSystem.covered` (definitions bundle `OAIQ053K006` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.Coverage.reduction_from_projections_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Hardness/Lists.lean (declaration OAI.MetricKMedian.Coverage.ProjectionSystem.coverage_agreement_bound)

import Mathlib
import Definitions.Def_OAIQ053K006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage.ProjectionSystem
open Finset

variable {U V I A B : Type} [Fintype U] [Fintype V] [Fintype I]
  [Fintype A] [Fintype B] [DecidableEq U] [DecidableEq V] [DecidableEq I]
  [DecidableEq A] [DecidableEq B]
variable (G : ProjectionSystem U V I A B)

theorem coverage_agreement_bound_s53 {d : ℕ} (hreg : G.LeftRegular d)
    (hI : 1 < Fintype.card I) (hdup : G.DuplicateConsistent)
    (S : Finset (U × A)) (hS : S.card ≤ Fintype.card U)
    {t : ℕ} (ht : 1 ≤ t) (default : A)
    (γ : ℝ) (hsound : ∀ left, ((G.agreement left).card:ℝ) ≤ γ*Fintype.card V) :
    ((G.covered S).card:ℝ) ≤
      (1-(1-1/(Fintype.card I:ℝ))^Fintype.card I+
        (Fintype.card I:ℝ)/t+(t:ℝ)^2*γ) *
        ((Fintype.card V:ℝ)*(Fintype.card I:ℝ)^Fintype.card B) := by
  sorry

end MetricKMedian.Coverage.ProjectionSystem

end Inline_PCPInherited

end OAI
end
