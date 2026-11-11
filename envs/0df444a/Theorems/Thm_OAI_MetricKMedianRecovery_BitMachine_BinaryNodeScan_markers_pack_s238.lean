-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryNodeScan_markers_pack_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryNodeScan.markers_pack_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:56:27.337768+00:00
-- url     : https://prove2.me/theorems/77a239f7-44e6-44ef-b646-94170c04b267
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryNodeScan.markers_pack_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryNodeScan.markers_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/FirstPresent.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/FirstPresent.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryNodeScan`, with `open WordOperations WordList RationalLeaves CanonicalMergeRefinement CanonicalMergeCrossing`, `open BinaryCross (ctxBits nodeBits resultBits)`, `open BinaryFiniteMachine (historyBits)`, `open BinaryOpeningPayment (field field_computes )`):
--
--   ```lean
--   lemma markers_pack_s238 {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ) (U : List (List (Label (Fin m))))
--       (a : List (Label (Fin m)) × List (List (Label (Fin m))))
--       (T : List (List (Label (Fin m)) × List (List (Label (Fin m))))) :
--       markers (pack F Q k U (a::T))=encode ((slots (transition F Q k) a T++[none]).map (FirstPresent.marker resultBits))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.WordList.encode` (definitions bundle `Q238K001` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.Label` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.CanonicalMergeCrossing.Result` (definitions bundle `Q238K003` of this split); `OAI.MetricKMedianRecovery.CanonicalMergeCrossing.slots` and `OAI.MetricKMedianRecovery.BitMachine.WordList.FirstPresent.marker` (definitions bundle `Q238K004` of this split); `OAI.MetricKMedianRecovery.CanonicalMergeCrossing.transition` (definitions bundle `Q238K014` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.resultBits` and `OAI.MetricKMedianRecovery.BitMachine.BinaryNodeScan.pack` (definitions bundle `Q238K021` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryNodeScan.markers` (definitions bundle `Q238K034` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteCross.run_pack_s238` and `OAI_MetricKMedianRecovery_BitMachine_BinaryScan_run_pack_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/FirstPresent.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryNodeScan.markers_pack)

import Mathlib
import Definitions.Def_Q238K034

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryNodeScan
open WordOperations WordList RationalLeaves CanonicalMergeRefinement CanonicalMergeCrossing
open BinaryCross (ctxBits nodeBits resultBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes )
attribute [local irreducible] BinaryCross.transition
lemma markers_pack_s238 {m : ℕ} (F Q : Finset (Label (Fin m))) (k : ℕ) (U : List (List (Label (Fin m))))
    (a : List (Label (Fin m)) × List (List (Label (Fin m))))
    (T : List (List (Label (Fin m)) × List (List (Label (Fin m))))) :
    markers (pack F Q k U (a::T))=encode ((slots (transition F Q k) a T++[none]).map (FirstPresent.marker resultBits)) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryNodeScan

end OAI
end
