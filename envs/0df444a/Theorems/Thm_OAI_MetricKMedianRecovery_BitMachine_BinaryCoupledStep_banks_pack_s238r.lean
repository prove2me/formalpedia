-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCoupledStep_banks_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.banks_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:44:04.249178+00:00
-- url     : https://prove2.me/theorems/cb92e850-8d3e-4017-90a8-c23aa359e994
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.banks_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.banks_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/StepPack.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/StepPack.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep`, with `open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge PhaseHistoryTransfer`, `open BinaryOpeningPayment (field field_encode)`, `open BinaryFiniteContext (labels setBits)`, `open BinaryFiniteMachine (historyBits)`, `open BinaryCoupled (stateBits outcomeBits)`):
--
--   ```lean
--   lemma banks_pack_s238r : banks xx=setBits (CanonicalCoupledMerge.banks F s.mapFree q)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLeaves.Label` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.original` (definitions bundle `Q238L008` of this split); `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.State` and `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.State.mapFree` (definitions bundle `Q238L019` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.pack` and `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.setBits` (definitions bundle `Q238L025` of this split); `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.banks` (definitions bundle `Q238L026` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.banks` and `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.pack` (definitions bundle `Q238L029` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.run_pack_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/StepPack.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.banks_pack)

import Mathlib
import Definitions.Def_Q238L026
import Definitions.Def_Q238L029

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCoupledStep
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge PhaseHistoryTransfer
open BinaryOpeningPayment (field field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryCoupled (stateBits outcomeBits)
variable {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m) (F : Finset (Fin m))
  (Q₀ : Finset (Label (Fin m))) (v z b : ℚ) (n q precision k : ℕ) (s : State (Fin m))
local notation "xx" => pack (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) Q₀ v z 0) n q b precision k s
lemma banks_pack_s238r : banks xx=setBits (CanonicalCoupledMerge.banks F s.mapFree q) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryCoupledStep

end OAI
end
