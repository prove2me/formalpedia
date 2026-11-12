-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryBranchRandomize_labels_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.labels_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:57:07.095931+00:00
-- url     : https://prove2.me/theorems/5fe61483-d3c1-4a7b-b251-112e1ea462e6
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.labels_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.labels_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Branching/BranchSeedLayout.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/BranchSeedLayout.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize`, with `open WordOperations WordList BinaryArithmetic BinaryBranchContext`, `open BinaryOpeningPayment (field field_computes )`):
--
--   ```lean
--   lemma labels_pack_s238r (hm : 0 < m) : labels input=BinaryFinSet.table (fun i=>ColorLabel.label m hm (seed.1.2 i))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalSampling.State` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.ColorLabel.label` and `OAI.MetricKMedianRecovery.ColorLabel.labelRange` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.Seed`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchTape.raw`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.table` and `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.Bits` (definitions bundle `Q238L018` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.pack` (definitions bundle `Q238L024` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.labels` (definitions bundle `Q238L034` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRecovery`).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.context_pack_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/BranchSeedLayout.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.labels_pack)

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L034

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchRandomize
open WordOperations WordList BinaryArithmetic BinaryBranchContext
open BinaryOpeningPayment (field field_computes )
attribute [local irreducible] Count.run BinaryBisection.logWord RawTake.run RawDrop.run BinaryColorLabel.colors BinaryColorLabel.labels
section Exact
variable {n m : ℕ} (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n)
    (colors0 : Fin n→Fin 3) (label0 : Fin n→Fin m) (q c : ℕ) (extra : List Bool)
local notation "data" => pack δ D F S Δ s colors0 label0 q c extra
variable (seed : BinaryBranchTape.Seed n m s.leaves.length)
local notation "input" => pairBits (data,BinaryBranchTape.raw seed)
lemma labels_pack_s238r (hm : 0 < m) : labels input=BinaryFinSet.table (fun i=>ColorLabel.label m hm (seed.1.2 i)) := by
  sorry
end Exact
end MetricKMedianRecovery.BitMachine.BinaryBranchRandomize

end OAI
end
