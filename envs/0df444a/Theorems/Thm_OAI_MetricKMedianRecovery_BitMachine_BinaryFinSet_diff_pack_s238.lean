-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryFinSet_diff_pack_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.diff_pack_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:38:36.830263+00:00
-- url     : https://prove2.me/theorems/1d97ef04-d858-481c-b4c3-4207e684c9d7
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.diff_pack_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.diff_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Encoding/FinSets.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Encoding/FinSets.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet`, with `open WordOperations WordList`):
--
--   ```lean
--   lemma diff_pack_s238 (S T : Finset (Fin n)) : BinaryNatSet.diff (pairBits (encode S,encode T))=encode (S\T)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.encode` (definitions bundle `Q238K010` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryNatSet.diff` (definitions bundle `Q238K025` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRefinedRecovery`).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCell.op_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchCheck.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.bluePack_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.completion_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.rowInput_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.run_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Client.radii_pair_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.ball_pair_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.remove_pair_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.run_pair_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Weights.weight_pair_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.check_pack_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.completion_pack_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Encoding/FinSets.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.diff_pack)

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K025

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFinSet
open WordOperations WordList
variable {n : ℕ}
lemma diff_pack_s238 (S T : Finset (Fin n)) : BinaryNatSet.diff (pairBits (encode S,encode T))=encode (S\T) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryFinSet

end OAI
end
