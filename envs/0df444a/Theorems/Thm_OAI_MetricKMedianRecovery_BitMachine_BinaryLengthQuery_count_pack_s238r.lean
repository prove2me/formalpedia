-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryLengthQuery_count_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryLengthQuery.count_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T12:12:53.350772+00:00
-- url     : https://prove2.me/theorems/dc2149fc-362e-422f-9ce2-d576c6ee1be3
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryLengthQuery.count_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryLengthQuery.count_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Machines/LengthQuery.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/LengthQuery.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryLengthQuery`, with `open WordOperations WordList BinaryArithmetic RationalLeaves`, `open BinaryFiniteContext (labels setBits)`, `open BinaryFiniteMachine (historyBits)`, `open BinaryOpeningPayment (field field_computes field_encode)`):
--
--   ```lean
--   lemma count_pack_s238r {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Label (Fin m))
--       (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (n q key : ℕ) (i : Label (Fin m)) (b s : ℚ)
--       (T U : List (List (Label (Fin m)))) :
--       count (pairBits (ctxBits (BinaryFiniteContext.pack distance loc F Q v z lam) n q key i b T U,BinaryRational.encode s))=
--         (CanonicalLengthSearch.count F Q (leaf key (parent i))
--           (fun s=>FiniteLabelContinuation.continuation loc (rows distance) F v lam q n (insert (leaf key (parent i) s) Q)) T U b s).bits
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.BinaryRational.encode` (definitions bundle `Q238L001` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.Label` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.CanonicalLengthSearch.count` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.parent` (definitions bundle `Q238L008` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder` and `OAI.MetricKMedianRecovery.RationalLeaves.leaf` (definitions bundle `Q238L019` of this split); `OAI.MetricKMedianRecovery.FiniteLabelContinuation.continuation` and `OAI.MetricKMedianRecovery.RationalLeaves.rows` (definitions bundle `Q238L020` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.pack` (definitions bundle `Q238L029` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryLengthQuery.ctxBits` (definitions bundle `Q238L030` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryLengthQuery.count` (definitions bundle `Q238L043` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRecovery`).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinarySensitive.run_pack_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/LengthQuery.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryLengthQuery.count_pack)

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L043

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryLengthQuery
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinaryFiniteMachine.continuation

lemma count_pack_s238r {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (n q key : ℕ) (i : Label (Fin m)) (b s : ℚ)
    (T U : List (List (Label (Fin m)))) :
    count (pairBits (ctxBits (BinaryFiniteContext.pack distance loc F Q v z lam) n q key i b T U,BinaryRational.encode s))=
      (CanonicalLengthSearch.count F Q (leaf key (parent i))
        (fun s=>FiniteLabelContinuation.continuation loc (rows distance) F v lam q n (insert (leaf key (parent i) s) Q)) T U b s).bits := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryLengthQuery

end OAI
end
