-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_IntegralCandidates_separated_comparison_s238
-- name    : OAI.MetricKMedianRecovery.IntegralCandidates.separated_comparison_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:23:04.358389+00:00
-- url     : https://prove2.me/theorems/fe44d97f-c311-491c-98f6-6b284382c32c
-- title:
--   OAI.MetricKMedianRecovery.IntegralCandidates.separated_comparison_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.IntegralCandidates.separated_comparison` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/AllBad.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/AllBad.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.IntegralCandidates`, with `open LocalSearch Anchoring Completion Sampling`):
--
--   ```lean
--   theorem separated_comparison_s238 (F D O S : Finset V) (hO : O.Nonempty) (hS : S.Nonempty)
--       (hO2 : 2 ≤ O.card) (hOF : O ⊆ F) (hSF : S ⊆ F) (hcard : S.card = O.card)
--       (hlocal : WidthLocalMin F D S 5) (beta : ℝ) (hbeta : 0 < beta) (hP : 0 < cost D O)
--       (hsep : ∀ i ∈ O, beta*cost D O ≤
--         ((Anchoring.cluster D (LocalSearch.nearest O hO) i).card:ℝ)*separation O i) :
--       ∃ C : Comparison D S O,
--         C.assign = LocalSearch.nearest O hO ∧ (C.bad.card:ℝ) ≤ countConstant (1/100)/beta
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Anchoring.cluster`, `OAI.MetricKMedianRecovery.Anchoring.countConstant`, `OAI.MetricKMedianRecovery.Anchoring.separation` and `OAI.MetricKMedianRecovery.LocalSearch.nearest` (definitions bundle `Q238K000` of this split); `OAI.MetricKMedianRecovery.Sampling.Comparison` (definitions bundle `Q238K004` of this split); `OAI.MetricKMedianRecovery.LocalSearch.WidthLocalMin`, `OAI.MetricKMedianRecovery.LocalSearch.cost` and `OAI.MetricKMedianRecovery.Sampling.Comparison.bad` (definitions bundle `Q238K015` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryIntegralAll.finite_program_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/AllBad.lean (declaration OAI.MetricKMedianRecovery.IntegralCandidates.separated_comparison)

import Mathlib
import Definitions.Def_Q238K015

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.IntegralCandidates
open LocalSearch Anchoring Completion Sampling
variable {V : Type*} [MetricSpace V] [LinearOrder V] [Fintype V]

omit [Fintype V] in

theorem separated_comparison_s238 (F D O S : Finset V) (hO : O.Nonempty) (hS : S.Nonempty)
    (hO2 : 2 ≤ O.card) (hOF : O ⊆ F) (hSF : S ⊆ F) (hcard : S.card = O.card)
    (hlocal : WidthLocalMin F D S 5) (beta : ℝ) (hbeta : 0 < beta) (hP : 0 < cost D O)
    (hsep : ∀ i ∈ O, beta*cost D O ≤
      ((Anchoring.cluster D (LocalSearch.nearest O hO) i).card:ℝ)*separation O i) :
    ∃ C : Comparison D S O,
      C.assign = LocalSearch.nearest O hO ∧ (C.bad.card:ℝ) ≤ countConstant (1/100)/beta := by
  sorry

end MetricKMedianRecovery.IntegralCandidates

end OAI
end
