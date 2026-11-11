-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCoupledStep_finishInput_pack_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.finishInput_pack_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:10:05.216222+00:00
-- url     : https://prove2.me/theorems/7942d588-469c-4412-bc24-55f30a1aa0ec
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.finishInput_pack_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.finishInput_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/StepPack.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/StepPack.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep`, with `open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge PhaseHistoryTransfer`, `open BinaryOpeningPayment (field field_encode)`, `open BinaryFiniteContext (labels setBits)`, `open BinaryFiniteMachine (historyBits)`, `open BinaryCoupled (stateBits outcomeBits)`):
--
--   ```lean
--   lemma finishInput_pack_s238 (H₀ G₀ : List (Label (Fin m))) (T₀ U₀ : List (List (Label (Fin m))))
--       (hT : s.T=H₀::T₀) (hU : s.U=G₀::U₀) : finishInput xx=encode
--         [setBits s.mapFree,BinaryRational.encode s.lam',historyBits (s.mapPrefix++[G₀]),historyBits (WW G₀)]
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.BinaryRational.encode` and `OAI.MetricKMedianRecovery.BitMachine.WordList.encode` (definitions bundle `Q238K001` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.Label` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.PhaseHistoryTransfer.after` (definitions bundle `Q238K004` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.original` (definitions bundle `Q238K017` of this split); `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.State`, `OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder`, `OAI.MetricKMedianRecovery.RationalLeaves.rows`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.setBits` and `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteMachine.historyBits` (definitions bundle `Q238K021` of this split); `OAI.MetricKMedianRecovery.FiniteLabelContinuation.continuation` (definitions bundle `Q238K022` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.pack`, `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.State.mapFree` and `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.State.mapPrefix` (definitions bundle `Q238K026` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.finishInput` (definitions bundle `Q238K043` of this split).
--
--   **Used by.** The proofs of `OAI_MetricKMedianRecovery_BitMachine_BinaryCoupledLoop_step_pack_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.run_pack_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/StepPack.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.finishInput_pack)

import Mathlib
import Definitions.Def_Q238K043

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
attribute [local irreducible] BinaryFiniteMachine.continuation BinaryFiniteCross.run
variable {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m) (F : Finset (Fin m))
  (Q₀ : Finset (Label (Fin m))) (v z b : ℚ) (n q precision k : ℕ) (s : State (Fin m))
local notation "xx" => pack (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) Q₀ v z 0) n q b precision k s
local notation "WW" => (fun G₀ : List (Label (Fin m)) => FiniteLabelContinuation.continuation (fun j=>original (loc j)) (rows distance)
  (F.image original) v s.lam' (q+1) n (after ∅ s.mapPrefix∪List.toFinset G₀))
lemma finishInput_pack_s238 (H₀ G₀ : List (Label (Fin m))) (T₀ U₀ : List (List (Label (Fin m))))
    (hT : s.T=H₀::T₀) (hU : s.U=G₀::U₀) : finishInput xx=encode
      [setBits s.mapFree,BinaryRational.encode s.lam',historyBits (s.mapPrefix++[G₀]),historyBits (WW G₀)] := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryCoupledStep

end OAI
end
