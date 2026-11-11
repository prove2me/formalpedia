-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCompletionAlgorithm_sixtyTwoFin_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionAlgorithm.sixtyTwoFin_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:18:02.491845+00:00
-- url     : https://prove2.me/theorems/fab14ad5-b28a-47b5-9a88-f222fc742b93
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionAlgorithm.sixtyTwoFin_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionAlgorithm.sixtyTwoFin` of [lean/OAI/Combinatorics/KMedianRecovery/Branching/BranchChecksCorrect.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/BranchChecksCorrect.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionAlgorithm`, with `open Categorical.Explicit`, `open MetricKMedianRecovery.Categorical`):
--
--   ```lean
--   lemma sixtyTwoFin_s238 (part : Fin q→Fin a) (rule : Selected.Rule part) (g : SetFunction (Fin q))
--       (hmono : Monotone g) (hsub : Diminishing g) (hg0 : g ∅=0)
--       (X : Finset (Fin q)) (hX : PartitionFeasible part X) :
--       (62/100:ℝ)*g X ≤ FiniteSampling.average
--         (fun bits : BinaryOracleIndex (Fin q) a (exponent a) (samples q a)→Bool =>
--           g (Selected.binaryGreedyOutput part rule g bits))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Categorical.BinaryOracleIndex`, `OAI.MetricKMedianRecovery.Categorical.SetFunction`, `OAI.MetricKMedianRecovery.FiniteSampling.average`, `OAI.MetricKMedianRecovery.Categorical.Explicit.exponent`, `OAI.MetricKMedianRecovery.Categorical.Explicit.samples` and `OAI.MetricKMedianRecovery.Categorical.Selected.Rule` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.Categorical.PartitionFeasible` (definitions bundle `Q238K004` of this split); `OAI.MetricKMedianRecovery.Categorical.Diminishing`, `OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq`, `OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype` and `OAI.MetricKMedianRecovery.Categorical.Selected.binaryGreedyOutput` (definitions bundle `Q238K014` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionFair.result_guarantee_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/BranchChecksCorrect.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionAlgorithm.sixtyTwoFin)

import Mathlib
import Definitions.Def_Q238K014

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletionAlgorithm
open Categorical.Explicit
open MetricKMedianRecovery.Categorical
variable {q a p r : ℕ}
attribute [local irreducible] exponent samples
lemma sixtyTwoFin_s238 (part : Fin q→Fin a) (rule : Selected.Rule part) (g : SetFunction (Fin q))
    (hmono : Monotone g) (hsub : Diminishing g) (hg0 : g ∅=0)
    (X : Finset (Fin q)) (hX : PartitionFeasible part X) :
    (62/100:ℝ)*g X ≤ FiniteSampling.average
      (fun bits : BinaryOracleIndex (Fin q) a (exponent a) (samples q a)→Bool =>
        g (Selected.binaryGreedyOutput part rule g bits)) := by
  sorry

end MetricKMedianRecovery.BitMachine.BinaryCompletionAlgorithm

end OAI
end
