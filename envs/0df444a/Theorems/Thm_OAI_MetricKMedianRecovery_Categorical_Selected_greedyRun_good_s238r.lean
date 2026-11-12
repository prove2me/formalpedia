-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_Categorical_Selected_greedyRun_good_s238r
-- name    : OAI.MetricKMedianRecovery.Categorical.Selected.greedyRun_good_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:25:59.917747+00:00
-- url     : https://prove2.me/theorems/8b32ea3d-7b3f-4f8d-8b46-1e54c336cde9
-- title:
--   OAI.MetricKMedianRecovery.Categorical.Selected.greedyRun_good_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.Categorical.Selected.greedyRun_good` of [lean/OAI/Combinatorics/KMedianRecovery/Branching/CategoricalRule.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/CategoricalRule.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.Categorical.Selected`, with `open FiniteSampling`):
--
--   ```lean
--   lemma greedyRun_good_s238r [NeZero T] (part : E → Fin a) (rule : Rule part)
--       (g : SetFunction E) (o : Fin a → E) (ho : ∀ j, part (o j) = j)
--       (hmono : Monotone g) (hsub : Diminishing g) (hg0 : g ∅ = 0)
--       {M tau : ℝ} (hM : 0 ≤ M) (hMo : M ≤ g (Finset.univ.image o))
--       (hg : BoundedMarginals g M) (ha : 0 < a) (htau : 0 ≤ tau) (htau1 : tau ≤ 1/8)
--       (hscale : (a:ℝ)^2 ≤ tau*T) (seed : Fin T → OracleSeed E a T L)
--       (hgood : ¬adaptiveBad (greedyStep part rule g) (estimationBad part g M tau)
--         T (initialState E a T) seed) :
--       (1 - 1/Real.exp 1 - 3*tau) * g (Finset.univ.image o) ≤
--         tableValue g (greedyRun part rule g seed).2
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Categorical.GreedyState`, `OAI.MetricKMedianRecovery.Categorical.OracleSeed`, `OAI.MetricKMedianRecovery.Categorical.SetFunction`, `OAI.MetricKMedianRecovery.Categorical.Table`, `OAI.MetricKMedianRecovery.Categorical.initialState`, `OAI.MetricKMedianRecovery.Categorical.Selected.Rule`, `OAI.MetricKMedianRecovery.Categorical.Selected.greedyRun` and `OAI.MetricKMedianRecovery.Categorical.Selected.greedyStep` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.FiniteSampling.adaptiveBad` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.Categorical.BoundedMarginals`, `OAI.MetricKMedianRecovery.Categorical.Diminishing`, `OAI.MetricKMedianRecovery.Categorical.estimationBad` and `OAI.MetricKMedianRecovery.Categorical.tableValue` (definitions bundle `Q238L010` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.Categorical.Selected.binaryGreedyOutput_expected_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/CategoricalRule.lean (declaration OAI.MetricKMedianRecovery.Categorical.Selected.greedyRun_good)

import Mathlib
import Definitions.Def_Q238L010

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Categorical.Selected
open FiniteSampling
variable {E : Type*} [Fintype E] [DecidableEq E] {a T L : ℕ}

lemma greedyRun_good_s238r [NeZero T] (part : E → Fin a) (rule : Rule part)
    (g : SetFunction E) (o : Fin a → E) (ho : ∀ j, part (o j) = j)
    (hmono : Monotone g) (hsub : Diminishing g) (hg0 : g ∅ = 0)
    {M tau : ℝ} (hM : 0 ≤ M) (hMo : M ≤ g (Finset.univ.image o))
    (hg : BoundedMarginals g M) (ha : 0 < a) (htau : 0 ≤ tau) (htau1 : tau ≤ 1/8)
    (hscale : (a:ℝ)^2 ≤ tau*T) (seed : Fin T → OracleSeed E a T L)
    (hgood : ¬adaptiveBad (greedyStep part rule g) (estimationBad part g M tau)
      T (initialState E a T) seed) :
    (1 - 1/Real.exp 1 - 3*tau) * g (Finset.univ.image o) ≤
      tableValue g (greedyRun part rule g seed).2 := by
  sorry

end MetricKMedianRecovery.Categorical.Selected

end OAI
end
