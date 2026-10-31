-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_NativeHashQueries_literal_trial_count
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.literal_trial_count
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:31:40.945862+00:00
-- url     : https://prove2.me/theorems/1cdcf9bd-e46d-4c31-95e0-dffde0c6983e
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.literal_trial_count: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.literal_trial_count` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeHashQueries.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeHashQueries.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries`, with `open BitProgram StructuredCalls SqrtLog DisjointReuse`, `open HighFrontendSources HashGreedyCode HashQueryEntry LeafProgram`, `open HashGreedyProgram.NativeRound`, `open LeafParametersProgram HighMarkedFrontend HighQuerySetup ProducedQueryResources`):
--
--   ```lean
--   theorem literal_trial_count {n B : ℕ} (F : RawCNF n) (hm : 0 < F.length)
--       (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
--       (rounds : ℕ) (word : List Bool) (e : Fin F.length) (d : State 40 896)
--       (h : n = BinaryArithmetic.toNat (trialQuery F hm shifts Q rounds word e d).ambient)
--       (hsource : (trialQuery F hm shifts Q rounds word e d).clauses =
--         HashInputProgram.Expansion.encodedClauses (Eq.mp (congrArg RawCNF h) F)) :
--       literalCount (trialQuery F hm shifts Q rounds word e d)
--         (Eq.mp (congrArg RawCNF h) F) hsource =
--         markedCount (HashGreedyCNF.rowAccept (NativeLeafSemantics.indexed F))
--           (HashGreedyCandidate.candidate F.length (SparseCode.distanceDenom F.length B)
--             (CounterPrograms.value word) :: HashGreedyCNF.history (NativeLeafSemantics.indexed F)
--               (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds)
--           (fun i x => !(NativeLeafSemantics.indexed F i).eval x) e
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.CounterPrograms.value` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.ExecCNF.Clause` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.distanceDenom` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query` (definitions bundle `OAIQ081S037` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.markedCount` (definitions bundle `OAIQ081S039` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.SuppliedLocal` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.SuppliedShifts` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Expansion.encodedClauses` (definitions bundle `OAIQ081S051` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.RawCNF` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF.rowAccept` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCode.initial` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSemantics.indexed` (definitions bundle `OAIQ081S081` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF.history` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCandidate.candidate` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashQueryEntry.trialQuery` (definitions bundle `OAIQ081S172` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.literalCount` (definitions bundle `OAIQ081S185` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat`, `OAI.Algorithms.SubexponentialSAT.SAT.Assignment`, `OAI.Algorithms.SubexponentialSAT.SAT.Literal` and `OAI.Algorithms.SubexponentialSAT.SAT.Clause.eval` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/NativeHashQueries.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.literal_trial_count)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S185

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries

open BitProgram StructuredCalls SqrtLog DisjointReuse
open HighFrontendSources HashGreedyCode HashQueryEntry LeafProgram
open HashGreedyProgram.NativeRound

open LeafParametersProgram HighMarkedFrontend HighQuerySetup ProducedQueryResources

theorem literal_trial_count {n B : ℕ} (F : RawCNF n) (hm : 0 < F.length)
    (shifts : SparseCode.SuppliedShifts F.length B) (Q : SparseCode.SuppliedLocal F.length B)
    (rounds : ℕ) (word : List Bool) (e : Fin F.length) (d : State 40 896)
    (h : n = BinaryArithmetic.toNat (trialQuery F hm shifts Q rounds word e d).ambient)
    (hsource : (trialQuery F hm shifts Q rounds word e d).clauses =
      HashInputProgram.Expansion.encodedClauses (Eq.mp (congrArg RawCNF h) F)) :
    literalCount (trialQuery F hm shifts Q rounds word e d)
      (Eq.mp (congrArg RawCNF h) F) hsource =
      markedCount (HashGreedyCNF.rowAccept (NativeLeafSemantics.indexed F))
        (HashGreedyCandidate.candidate F.length (SparseCode.distanceDenom F.length B)
          (CounterPrograms.value word) :: HashGreedyCNF.history (NativeLeafSemantics.indexed F)
            (SparseCode.distanceDenom F.length B) (initial shifts Q) rounds)
        (fun i x => !(NativeLeafSemantics.indexed F i).eval x) e := by
  sorry

open NativeQueryInputBounds Statement

attribute [local irreducible] Execute.guardedModel

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries
end
