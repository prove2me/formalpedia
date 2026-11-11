-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCross_finalCount_pack_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryCross.finalCount_pack_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:54:09.11662+00:00
-- url     : https://prove2.me/theorems/0c8f4d85-2b85-47f1-9d61-f6887441825b
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryCross.finalCount_pack_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.finalCount_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/CrossCount.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/CrossCount.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryCross`, with `open WordOperations WordList RationalLeaves BinaryArithmetic`, `open BinaryFiniteContext (labels setBits)`, `open BinaryFiniteMachine (historyBits)`, `open BinaryOpeningPayment (field field_computes )`):
--
--   ```lean
--   lemma finalCount_pack_s238 {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ)
--       (H : List (Label (Fin m))) (T : List (List (Label (Fin m)))) :
--       finalCount (pairBits (ctxBits F Q k,nodeBits (H,T)))=(CanonicalMergeCrossing.finalCount F Q H T).bits
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLeaves.Label` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.CanonicalMergeCrossing.finalCount` (definitions bundle `Q238K004` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.ctxBits` and `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.nodeBits` (definitions bundle `Q238K021` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.finalCount` (definitions bundle `Q238K034` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRefinedRecovery`).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.c_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.edge_pack_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinaryNodeScan.markers_pack_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/CrossCount.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryCross.finalCount_pack)

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K034

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCross
open WordOperations WordList RationalLeaves BinaryArithmetic
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes )

lemma finalCount_pack_s238 {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ)
    (H : List (Label (Fin m))) (T : List (List (Label (Fin m)))) :
    finalCount (pairBits (ctxBits F Q k,nodeBits (H,T)))=(CanonicalMergeCrossing.finalCount F Q H T).bits := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryCross

end OAI
end
