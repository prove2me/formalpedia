-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryScan_nodes_pack_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryScan.nodes_pack_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:13:27.377206+00:00
-- url     : https://prove2.me/theorems/5505c955-07b4-445d-9aeb-e774c7cd40ad
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryScan.nodes_pack_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryScan.nodes_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Machines/ScanMachine.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/ScanMachine.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryScan`, with `open WordOperations WordList RationalLeaves CanonicalMergeCrossing`, `open BinaryCross (ctxBits nodeBits resultBits)`, `open BinaryFiniteContext (labels setBits)`, `open BinaryFiniteMachine (historyBits)`, `open BinaryOpeningPayment (field field_computes field_encode)`):
--
--   ```lean
--   lemma nodes_pack_s238 {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
--       (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (k n q : ℕ)
--       (U : List (List (Label (Fin m)))) (H : List (Label (Fin m))) (T S : List (List (Label (Fin m)))) :
--       nodes (pack (BinaryFiniteContext.pack distance loc F Q v z lam) F Q k n q U H T S)=
--         encode (((H,T)::S.map (fun J=>(J,FiniteLabelContinuation.continuation loc (rows distance) F v lam q n
--           (Q∪J.toFinset)))).map nodeBits)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.WordList.encode` (definitions bundle `Q238K001` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.Label` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder`, `OAI.MetricKMedianRecovery.RationalLeaves.rows` and `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.nodeBits` (definitions bundle `Q238K021` of this split); `OAI.MetricKMedianRecovery.FiniteLabelContinuation.continuation` (definitions bundle `Q238K022` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.pack` and `OAI.MetricKMedianRecovery.BitMachine.BinaryScan.pack` (definitions bundle `Q238K026` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryScan.nodes` (definitions bundle `Q238K043` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteCross.run_pack_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/ScanMachine.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryScan.nodes_pack)

import Mathlib
import Definitions.Def_Q238K043

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryScan
open WordOperations WordList RationalLeaves CanonicalMergeCrossing
open BinaryCross (ctxBits nodeBits resultBits)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinaryFiniteMachine.continuation BinaryNodeScan.run
lemma nodes_pack_s238 {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (k n q : ℕ)
    (U : List (List (Label (Fin m)))) (H : List (Label (Fin m))) (T S : List (List (Label (Fin m)))) :
    nodes (pack (BinaryFiniteContext.pack distance loc F Q v z lam) F Q k n q U H T S)=
      encode (((H,T)::S.map (fun J=>(J,FiniteLabelContinuation.continuation loc (rows distance) F v lam q n
        (Q∪J.toFinset)))).map nodeBits) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryScan

end OAI
end
