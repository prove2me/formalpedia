-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryBranchCheck_run_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryBranchCheck.run_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:43:24.43421+00:00
-- url     : https://prove2.me/theorems/fd065001-9496-45a8-94fd-e9b3c393b4b4
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryBranchCheck.run_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchCheck.run_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Branching/BranchChecksCorrect.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/BranchChecksCorrect.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchCheck`, with `open WordList WordOperations BinaryArithmetic BinaryBranchContext`, `open BinaryOpeningPayment (field )`):
--
--   ```lean
--   lemma run_pack_s238r : run data=decide (Ready δ F S s colors k c m)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalSampling.State` and `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchCheck.Ready` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.pack` (definitions bundle `Q238L024` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchCheck.run` (definitions bundle `Q238L028` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.run_pack_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/BranchChecksCorrect.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryBranchCheck.run_pack)

import Mathlib
import Definitions.Def_Q238L028

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchCheck
attribute [local instance] Classical.propDecidable
open WordList WordOperations BinaryArithmetic BinaryBranchContext
open BinaryOpeningPayment (field )
variable {n m : ℕ}
section Correct
variable (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors : Fin n→Fin 3) (label : Fin n→Fin m) (k c : ℕ) (extra : List Bool)
local notation "data" => pack δ D F S Δ s colors label k c extra
lemma run_pack_s238r : run data=decide (Ready δ F S s colors k c m) := by
  sorry
end Correct
end MetricKMedianRecovery.BitMachine.BinaryBranchCheck

end OAI
end
