-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryRefine_cutOp_pack_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryRefine.cutOp_pack_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:56:59.082226+00:00
-- url     : https://prove2.me/theorems/9969cb19-e537-4f89-bcc6-781d1eafd708
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryRefine.cutOp_pack_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryRefine.cutOp_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Machines/RefineMachine.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/RefineMachine.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryRefine`, with `open WordOperations WordList RationalLeaves CanonicalMergeRefinement`, `open BinaryFiniteContext (labels setBits)`, `open BinaryFiniteMachine (historyBits)`, `open BinaryOpeningPayment (field field_computes field_encode)`):
--
--   ```lean
--   lemma cutOp_pack_s238 {m : ℕ} (F : Finset (Label (Fin m))) (R : List (Label (Fin m))) (key spare : ℕ)
--       (p : List (List (Label (Fin m))) × List (Label (Fin m)) × List (List (Label (Fin m)))) :
--       cutOp (pairBits (ctxBits F R key spare,Slices.cutBits labels p))=
--         historyBits (match p.2.2 with | []=>[] | G::_=>refinedEdge F R (copy key) (copy spare) p.2.1 G)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLeaves.Label` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.labels` (definitions bundle `Q238K010` of this split); `OAI.MetricKMedianRecovery.CanonicalMergeRefinement.refinedEdge` and `OAI.MetricKMedianRecovery.BitMachine.WordList.Slices.cutBits` (definitions bundle `Q238K014` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteMachine.historyBits` (definitions bundle `Q238K021` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.copy` (definitions bundle `Q238K026` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryRefine.ctxBits` (definitions bundle `Q238K027` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryRefine.cutOp` (definitions bundle `Q238K034` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRefinedRecovery`).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryRegularChain.run_pack_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/RefineMachine.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryRefine.cutOp_pack)

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K027
import Definitions.Def_Q238K034

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRefine
open WordOperations WordList RationalLeaves CanonicalMergeRefinement
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
lemma cutOp_pack_s238 {m : ℕ} (F : Finset (Label (Fin m))) (R : List (Label (Fin m))) (key spare : ℕ)
    (p : List (List (Label (Fin m))) × List (Label (Fin m)) × List (List (Label (Fin m)))) :
    cutOp (pairBits (ctxBits F R key spare,Slices.cutBits labels p))=
      historyBits (match p.2.2 with | []=>[] | G::_=>refinedEdge F R (copy key) (copy spare) p.2.1 G) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryRefine

end OAI
end
