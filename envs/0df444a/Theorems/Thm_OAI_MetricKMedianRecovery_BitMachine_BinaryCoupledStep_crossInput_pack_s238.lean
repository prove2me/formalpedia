-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCoupledStep_crossInput_pack_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.crossInput_pack_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:10:06.59551+00:00
-- url     : https://prove2.me/theorems/fe113572-8b68-4bac-8eb7-0fc9ba02bc91
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.crossInput_pack_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.crossInput_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/StepPack.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/StepPack.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep`, with `open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge PhaseHistoryTransfer`, `open BinaryOpeningPayment (field field_encode)`, `open BinaryFiniteContext (labels setBits)`, `open BinaryFiniteMachine (historyBits)`, `open BinaryCoupled (stateBits outcomeBits)`):
--
--   ```lean
--   lemma crossInput_pack_s238 (H₀ G₀ : List (Label (Fin m))) (T₀ U₀ : List (List (Label (Fin m))))
--       (hT : s.T=H₀::T₀) (hU : s.U=G₀::U₀) : crossInput xx=BinaryFiniteCross.pack
--         (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) (after ∅ s.mapPrefix) v ((1+v^2)^q) s.lam')
--         (3*q) (3*q+1) k n q H₀ G₀ T₀ (WW G₀)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLeaves.Label` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.PhaseHistoryTransfer.after` (definitions bundle `Q238K004` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.original` (definitions bundle `Q238K017` of this split); `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.State`, `OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder`, `OAI.MetricKMedianRecovery.RationalLeaves.rows` and `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteCross.pack` (definitions bundle `Q238K021` of this split); `OAI.MetricKMedianRecovery.FiniteLabelContinuation.continuation` (definitions bundle `Q238K022` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.pack`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.pack` and `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.State.mapPrefix` (definitions bundle `Q238K026` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.crossInput` (definitions bundle `Q238K043` of this split).
--
--   **Used by.** The proofs of `OAI_MetricKMedianRecovery_BitMachine_BinaryCoupledLoop_step_pack_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.run_pack_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/StepPack.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.crossInput_pack)

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
lemma crossInput_pack_s238 (H₀ G₀ : List (Label (Fin m))) (T₀ U₀ : List (List (Label (Fin m))))
    (hT : s.T=H₀::T₀) (hU : s.U=G₀::U₀) : crossInput xx=BinaryFiniteCross.pack
      (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) (after ∅ s.mapPrefix) v ((1+v^2)^q) s.lam')
      (3*q) (3*q+1) k n q H₀ G₀ T₀ (WW G₀) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryCoupledStep

end OAI
end
