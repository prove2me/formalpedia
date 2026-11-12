-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCross_edge_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryCross.edge_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T12:03:18.375807+00:00
-- url     : https://prove2.me/theorems/91012128-b755-4de9-8cb3-66a78a56621c
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryCross.edge_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.edge_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/CrossEdge.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/CrossEdge.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryCross`, with `open WordOperations WordList RationalLeaves BinaryArithmetic`, `open BinaryFiniteContext (labels setBits)`, `open BinaryFiniteMachine (historyBits)`, `open BinaryOpeningPayment (field field_computes field_encode)`):
--
--   ```lean
--   lemma edge_pack_s238r {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ)
--       (H G : List (Label (Fin m))) (T U : List (List (Label (Fin m)))) :
--       edge (pack F Q k (H,T) (G,U))=resultBits (CanonicalMergeCrossing.edge F Q k H G T U)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLeaves.Label` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.CanonicalMergeCrossing.edge` (definitions bundle `Q238L010` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.pack` and `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.resultBits` (definitions bundle `Q238L025` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.edge` (definitions bundle `Q238L037` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryNodeScan.markers_pack_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/CrossEdge.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryCross.edge_pack)

import Mathlib
import Definitions.Def_Q238L037

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
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] paid finalCount

lemma edge_pack_s238r {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ)
    (H G : List (Label (Fin m))) (T U : List (List (Label (Fin m)))) :
    edge (pack F Q k (H,T) (G,U))=resultBits (CanonicalMergeCrossing.edge F Q k H G T U) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryCross

end OAI
end
