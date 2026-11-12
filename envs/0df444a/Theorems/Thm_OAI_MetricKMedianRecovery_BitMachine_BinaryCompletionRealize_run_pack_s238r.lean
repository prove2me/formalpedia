-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCompletionRealize_run_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.run_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:57:08.558194+00:00
-- url     : https://prove2.me/theorems/b8c116ca-88f8-44df-9032-bb6791f533fa
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.run_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.run_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Branching/CompletionRealize.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/CompletionRealize.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize`, with `open WordOperations WordList BinaryArithmetic`, `open BinaryOpeningPayment (field field_computes )`):
--
--   ```lean
--   lemma run_pack_s238r : run data=BinaryFinSet.encode (Completion.Canonical.realize F S Q part o loc redLoc blueLoc blueDest xs (BinaryRationalSort.indexSet v k))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.capped`, `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalSort.indexSet` and `OAI.MetricKMedianRecovery.Completion.Canonical.realize` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.encode` (definitions bundle `Q238L017` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.pack` (definitions bundle `Q238L025` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.run` (definitions bundle `Q238L034` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.run_pack_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.run_pack_s238r` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/CompletionRealize.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryCompletionRealize.run_pack)

import Mathlib
import Definitions.Def_Q238L034

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletionRealize
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes )
variable {n q a p r b : ℕ}
attribute [local irreducible] fillInput BinaryCompletionFill.run BinaryFinSet.image
attribute [local irreducible] redValues BinaryNatSet.sort BinaryRationalSort.rawIndices
attribute [local irreducible] redIndices
attribute [local irreducible] red blue dest BinaryNatSet.union
attribute [local irreducible] removed BinaryNatSet.diff
attribute [local irreducible] filled
attribute [local irreducible] remain added
attribute [local irreducible] core
section Correct
variable (F S Q : Finset (Fin n)) (part : Fin q→Fin a) (o : Fin a→Fin q) (loc : Fin q→Fin n)
    (redLoc : Fin r→Fin n) (blueLoc blueDest : Fin b→Fin n) (k : ℕ)
    (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ) (weight redBase : Fin r→ℚ)
    (redDistance : Fin r→Fin q→ℚ) (xs : List (Fin q))
local notation "data" => pack F S Q part o loc redLoc blueLoc blueDest k base distance weight redBase redDistance xs
local notation "v" => (fun i=>weight i*BinaryCompletion.capped (redBase i) (redDistance i) xs.toFinset)
lemma run_pack_s238r : run data=BinaryFinSet.encode (Completion.Canonical.realize F S Q part o loc redLoc blueLoc blueDest xs (BinaryRationalSort.indexSet v k)) := by
  sorry
end Correct
end MetricKMedianRecovery.BitMachine.BinaryCompletionRealize

end OAI
end
