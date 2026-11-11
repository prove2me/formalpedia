-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryBranchContext_locations_pack_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.locations_pack_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:35:34.355202+00:00
-- url     : https://prove2.me/theorems/7e9b3c83-7631-4a16-a21c-8fc701c30ba9
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.locations_pack_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.locations_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Branching/BranchContext.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/BranchContext.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext`, with `open WordOperations WordList`, `open BinaryOpeningPayment (field )`):
--
--   ```lean
--   lemma locations_pack_s238 (hH : ∀ i,(H i).Nonempty) : locations data=BinaryFinSet.table (Completion.CopyGround.location H hH)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalSampling.State`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.balls` and `OAI.MetricKMedianRecovery.Completion.CopyGround.location` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.table` (definitions bundle `Q238K010` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.pack` (definitions bundle `Q238K020` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.locations` (definitions bundle `Q238K025` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.completion_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.rowInput_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryBranchProgram_rows_pack_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.completion_pack_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/BranchContext.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.locations_pack)

import Mathlib
import Definitions.Def_Q238K025

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchContext
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n m : ℕ}
attribute [local irreducible] remaining
attribute [local irreducible] classOf
attribute [local irreducible] ballInput
attribute [local irreducible] copyData
attribute [local irreducible] origins
attribute [local irreducible] locations
section Correct
variable (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors : Fin n→Fin 3) (label : Fin n→Fin m) (k c : ℕ) (extra : List Bool)
local notation "data" => pack δ D F S Δ s colors label k c extra
local notation "H" => balls δ F s
lemma locations_pack_s238 (hH : ∀ i,(H i).Nonempty) : locations data=BinaryFinSet.table (Completion.CopyGround.location H hH) := by
  sorry
end Correct
end MetricKMedianRecovery.BitMachine.BinaryBranchContext

end OAI
end
