-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryBranchProgram_bluePack_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.bluePack_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:54:29.54278+00:00
-- url     : https://prove2.me/theorems/3e2a9e18-ca96-4766-a19c-c3c5afb9d226
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.bluePack_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.bluePack_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Branching/CompletionFair.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/CompletionFair.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram`, with `open WordOperations WordList BinaryBranchContext`, `open BinaryOpeningPayment (field field_computes )`):
--
--   ```lean
--   lemma bluePack_pack_s238r : bluePack data=BinaryBlueProgram.pack extra (fun i : Fin n=>i.val.bits) blue F label score Finset.univ c
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalSampling.State` and `OAI.MetricKMedianRecovery.RationalSampling.assignmentWeight` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueProgram.pack` and `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.pack` (definitions bundle `Q238L024` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.bluePack` (definitions bundle `Q238L033` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.plan_pack_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.run_pack_s238r` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/CompletionFair.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.bluePack_pack)

import Mathlib
import Definitions.Def_Q238L033

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchProgram
open WordOperations WordList BinaryBranchContext
open BinaryOpeningPayment (field field_computes )
variable {n m : ℕ}
attribute [local irreducible] blueInput
attribute [local irreducible] records
attribute [local irreducible] bluePack
attribute [local irreducible] best
attribute [local irreducible] plan
attribute [local irreducible] rowInput
attribute [local irreducible] rows
attribute [local irreducible] completion
section Correct
variable (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors : Fin n→Fin 3) (label : Fin n→Fin m) (k c : ℕ) (extra : List Bool)
local notation "data" => BinaryBranchContext.pack δ D F S Δ s colors label k c extra
local notation "blue" => Finset.filter (fun i=>colors i=2) (S\RationalSampling.State.deleted s)
local notation "score" => (fun u v=>RationalSampling.assignmentWeight δ D S Δ s u*δ u v)
lemma bluePack_pack_s238r : bluePack data=BinaryBlueProgram.pack extra (fun i : Fin n=>i.val.bits) blue F label score Finset.univ c := by
  sorry
end Correct
end MetricKMedianRecovery.BitMachine.BinaryBranchProgram

end OAI
end
