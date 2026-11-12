-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryResolve_run_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryResolve.run_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T12:12:26.118455+00:00
-- url     : https://prove2.me/theorems/bbc8477e-9919-4e93-9ca8-e3ace0214709
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryResolve.run_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryResolve.run_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Machines/ResolveMachine.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/ResolveMachine.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryResolve`, with `open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge CanonicalLengthView`, `open BinaryOpeningPayment (field field_computes field_encode)`, `open BinaryFiniteContext (labels setBits)`, `open BinaryFiniteMachine (historyBits)`):
--
--   ```lean
--   lemma run_pack_s238r {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m) (F : Finset (Fin m))
--       (B : Finset (Label (Fin m))) (v z lam M : ℚ) (n q key N precision k : ℕ)
--       (P : List (List (Label (Fin m)))) (R : CanonicalMergeCrossing.Result (Label (Fin m))) :
--       run (pack (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) (PhaseHistoryTransfer.after ∅ P) v z lam)
--         n q key (20*N*M) k precision B P R)=
--         BinaryCoupled.outcomeBits (CanonicalCoupledMerge.resolve loc distance F v M N precision q n k key B lam P R)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLeaves.Label` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.CanonicalMergeCrossing.Result` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.PhaseHistoryTransfer.after` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.original` (definitions bundle `Q238L008` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupled.outcomeBits` (definitions bundle `Q238L025` of this split); `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.resolve` (definitions bundle `Q238L026` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.pack` (definitions bundle `Q238L029` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryResolve.pack` (definitions bundle `Q238L030` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryResolve.run` (definitions bundle `Q238L043` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.run_pack_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/ResolveMachine.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryResolve.run_pack)

import Mathlib
import Definitions.Def_Q238L043

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryResolve
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge CanonicalLengthView
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
lemma run_pack_s238r {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m) (F : Finset (Fin m))
    (B : Finset (Label (Fin m))) (v z lam M : ℚ) (n q key N precision k : ℕ)
    (P : List (List (Label (Fin m)))) (R : CanonicalMergeCrossing.Result (Label (Fin m))) :
    run (pack (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) (PhaseHistoryTransfer.after ∅ P) v z lam)
      n q key (20*N*M) k precision B P R)=
      BinaryCoupled.outcomeBits (CanonicalCoupledMerge.resolve loc distance F v M N precision q n k key B lam P R) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryResolve

end OAI
end
