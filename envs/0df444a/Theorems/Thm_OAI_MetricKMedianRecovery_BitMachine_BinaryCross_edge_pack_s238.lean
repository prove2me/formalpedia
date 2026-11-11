-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCross_edge_pack_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryCross.edge_pack_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:54:43.562286+00:00
-- url     : https://prove2.me/theorems/c40d0d9d-4980-42bd-b306-5d30665d957f
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryCross.edge_pack_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.edge_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/CrossEdge.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/CrossEdge.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryCross`, with `open WordOperations WordList RationalLeaves BinaryArithmetic`, `open BinaryFiniteContext (labels setBits)`, `open BinaryFiniteMachine (historyBits)`, `open BinaryOpeningPayment (field field_computes )`):
--
--   ```lean
--   lemma edge_pack_s238 {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ)
--       (H G : List (Label (Fin m))) (T U : List (List (Label (Fin m)))) :
--       edge (pack F Q k (H,T) (G,U))=resultBits (CanonicalMergeCrossing.edge F Q k H G T U)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLeaves.Label` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.CanonicalMergeCrossing.edge` (definitions bundle `Q238K014` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.pack` and `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.resultBits` (definitions bundle `Q238K021` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.edge` (definitions bundle `Q238K034` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryNodeScan.markers_pack_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/CrossEdge.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryCross.edge_pack)

import Mathlib
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
attribute [local irreducible] paid finalCount

lemma edge_pack_s238 {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ)
    (H G : List (Label (Fin m))) (T U : List (List (Label (Fin m)))) :
    edge (pack F Q k (H,T) (G,U))=resultBits (CanonicalMergeCrossing.edge F Q k H G T U) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryCross

end OAI
end
