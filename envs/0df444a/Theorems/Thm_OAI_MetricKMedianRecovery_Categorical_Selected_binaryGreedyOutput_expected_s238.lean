-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_Categorical_Selected_binaryGreedyOutput_expected_s238
-- name    : OAI.MetricKMedianRecovery.Categorical.Selected.binaryGreedyOutput_expected_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:19:46.369001+00:00
-- url     : https://prove2.me/theorems/145a1f59-201f-4362-91ee-04820f299b7d
-- title:
--   OAI.MetricKMedianRecovery.Categorical.Selected.binaryGreedyOutput_expected_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.Categorical.Selected.binaryGreedyOutput_expected` of [lean/OAI/Combinatorics/KMedianRecovery/Branching/CategoricalRule.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/CategoricalRule.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.Categorical.Selected`, with `open FiniteSampling`):
--
--   ```lean
--   lemma binaryGreedyOutput_expected_s238 {E : Type*} [Fintype E] [DecidableEq E]
--       {a b L : ℕ} (part : E → Fin a) (rule : Rule part)
--       (g : SetFunction E) (hmono : Monotone g) (hsub : Diminishing g) (hg0 : g ∅ = 0)
--       {tau : ℝ} (ha : 0 < a) (htau : 0 < tau) (htau1 : tau ≤ 1/8)
--       (hscale : (a:ℝ)^2 ≤ tau*(2^b:ℕ)) (hL : 0 < L)
--       (hcount : ((2^b:ℕ):ℝ)*Fintype.card E*a^2/(4*tau^3) ≤ L)
--       (S : Finset E) (hS : PartitionFeasible part S) :
--       (1 - 1/Real.exp 1 - 4*tau) * g S ≤
--         average (fun bits : BinaryOracleIndex E a b L → Bool =>
--           g (binaryGreedyOutput part rule g bits))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Categorical.BinaryOracleIndex`, `OAI.MetricKMedianRecovery.Categorical.SetFunction`, `OAI.MetricKMedianRecovery.FiniteSampling.average` and `OAI.MetricKMedianRecovery.Categorical.Selected.Rule` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.Categorical.PartitionFeasible` (definitions bundle `Q238K004` of this split); `OAI.MetricKMedianRecovery.Categorical.Diminishing`, `OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq`, `OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype` and `OAI.MetricKMedianRecovery.Categorical.Selected.binaryGreedyOutput` (definitions bundle `Q238K014` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionAlgorithm.sixtyTwoFin_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/CategoricalRule.lean (declaration OAI.MetricKMedianRecovery.Categorical.Selected.binaryGreedyOutput_expected)

import Mathlib
import Definitions.Def_Q238K014

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Categorical.Selected
open FiniteSampling
variable {E : Type*} [Fintype E] [DecidableEq E] {a T L : ℕ}

lemma binaryGreedyOutput_expected_s238 {E : Type*} [Fintype E] [DecidableEq E]
    {a b L : ℕ} (part : E → Fin a) (rule : Rule part)
    (g : SetFunction E) (hmono : Monotone g) (hsub : Diminishing g) (hg0 : g ∅ = 0)
    {tau : ℝ} (ha : 0 < a) (htau : 0 < tau) (htau1 : tau ≤ 1/8)
    (hscale : (a:ℝ)^2 ≤ tau*(2^b:ℕ)) (hL : 0 < L)
    (hcount : ((2^b:ℕ):ℝ)*Fintype.card E*a^2/(4*tau^3) ≤ L)
    (S : Finset E) (hS : PartitionFeasible part S) :
    (1 - 1/Real.exp 1 - 4*tau) * g S ≤
      average (fun bits : BinaryOracleIndex E a b L → Bool =>
        g (binaryGreedyOutput part rule g bits)) := by
  sorry

end MetricKMedianRecovery.Categorical.Selected

end OAI
end
