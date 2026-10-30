-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryExecution_replay_resources
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.replay_resources
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T02:17:30.497127+00:00
-- url     : https://prove2.me/theorems/1998e738-e93b-4cd7-9279-3a7df1b8afe5
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.replay_resources: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.replay_resources` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryExecution.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryExecution.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution`, with `open OAI BitProgram StructuredCalls`, `open QueryTupleVisitor SignatureTupleProgram`):
--
--   ```lean
--   theorem replay_resources (work : Code) (base C B D : ℕ)
--       (I : List (List Bool) → Data → Prop)
--       (step : ∀ word rest a, FrameCursor base (word::rest) a → I (word::rest) a →
--         (∀ i, (a.stacks i).length ≤ B) →
--         ∃ steps b, Eval work steps
--           (headState a word (suspendedFrames rest) (List.replicate (base+rest.length) true)) b ∧
--           steps ≤ C ∧ b.stacks 838=word ∧ b.stacks 840=suspendedFrames rest ∧
--           b.stacks 843=List.replicate (base+rest.length) true ∧ I rest (finished b) ∧
--           (∀ i, (b.stacks i).length ≤ B) ∧
--           PrefixBound work steps
--             (headState a word (suspendedFrames rest) (List.replicate (base+rest.length) true)) D)
--       (words : List (List Bool)) (a : Data)
--       (hreps : a.stacks 837=suspendedFrames words)
--       (haddress : a.stacks 845=List.replicate (base+words.length) true)
--       (hcurrent : a.stacks 838=[]) (hscratch : a.stacks 841=[])
--       (hi : I words (tested (restartState a)))
--       (ha : ∀ i, (a.stacks i).length ≤ B) :
--       ∃ steps b, Eval (replay work) steps a b ∧ FrameCursor base [] b ∧ I [] b ∧
--         (∀ i, (b.stacks i).length ≤ B) ∧
--         steps+1 ≤ 18*B+8*(words.map List.length).sum+(C+10)*words.length+19 ∧
--         PrefixBound (replay work) (steps+1) a (max D (914*B+18))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram.suspendedFrames` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.Code` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.replay` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.PrefixBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor.FrameCursor`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor.finished`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor.headState`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor.restartState` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor.tested` (definitions bundle `OAIQ081S178` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.baseline_pass` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.evaluation_pass` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryExecution.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.replay_resources)

import Mathlib
import Definitions.Def_OAIQ081S178

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution

open OAI BitProgram StructuredCalls
open QueryTupleVisitor SignatureTupleProgram

theorem replay_resources (work : Code) (base C B D : ℕ)
    (I : List (List Bool) → Data → Prop)
    (step : ∀ word rest a, FrameCursor base (word::rest) a → I (word::rest) a →
      (∀ i, (a.stacks i).length ≤ B) →
      ∃ steps b, Eval work steps
        (headState a word (suspendedFrames rest) (List.replicate (base+rest.length) true)) b ∧
        steps ≤ C ∧ b.stacks 838=word ∧ b.stacks 840=suspendedFrames rest ∧
        b.stacks 843=List.replicate (base+rest.length) true ∧ I rest (finished b) ∧
        (∀ i, (b.stacks i).length ≤ B) ∧
        PrefixBound work steps
          (headState a word (suspendedFrames rest) (List.replicate (base+rest.length) true)) D)
    (words : List (List Bool)) (a : Data)
    (hreps : a.stacks 837=suspendedFrames words)
    (haddress : a.stacks 845=List.replicate (base+words.length) true)
    (hcurrent : a.stacks 838=[]) (hscratch : a.stacks 841=[])
    (hi : I words (tested (restartState a)))
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    ∃ steps b, Eval (replay work) steps a b ∧ FrameCursor base [] b ∧ I [] b ∧
      (∀ i, (b.stacks i).length ≤ B) ∧
      steps+1 ≤ 18*B+8*(words.map List.length).sum+(C+10)*words.length+19 ∧
      PrefixBound (replay work) (steps+1) a (max D (914*B+18)) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution
end
