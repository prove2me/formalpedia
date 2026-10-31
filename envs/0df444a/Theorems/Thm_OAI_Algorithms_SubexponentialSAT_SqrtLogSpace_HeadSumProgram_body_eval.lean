-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HeadSumProgram_body_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.body_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:37:56.462516+00:00
-- url     : https://prove2.me/theorems/d661f062-e4aa-459f-a05c-8d1589a4f647
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.body_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.body_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadSumProgram.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadSumProgram.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram`, with `open OAI BitProgram StructuredCalls CounterPrograms`, `open HeadEvaluationProgram.StagedGate (copy copyState clear clearState )`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram OAI.Algorithms.SubexponentialSAT.SubexpLiftRing`, `open OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing TruncatedRingProgram`, `open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram`):
--
--   ```lean
--   theorem body_eval (accepted : Code) (a : Data) (rows : List (List (List Bool)))
--       (C : ℕ) (P : Data → Prop)
--       (hclean : ∀ i : Fin 32, a.stacks (HeadEvaluationProgram.StagedGate.stackMap i) = [])
--       (hmatrix : a.stacks 865 = words (rows.map words))
--       (hlen : ∀ row ∈ rows, row.length = (a.stacks 859).length)
--       (hE : (a.stacks 859).length = (a.stacks 867).length)
--       (hH : (a.stacks 859).length = (a.stacks 868).length)
--       (hs : a.stacks 861 = [])
--       (haccepted : gateValue a rows = true → ∀ out : Fin 40 → Bool, out 15 = true →
--         ∃ nb b, nb ≤ C ∧ Eval accepted nb ⟨out, a.stacks⟩ b ∧
--           b.stacks 859 = a.stacks 859 ∧ b.stacks 860 = a.stacks 860 ∧
--           b.stacks 861 = [] ∧ P b)
--       (hrejected : gateValue a rows = false → ∀ out : Fin 40 → Bool, P ⟨out, a.stacks⟩) :
--       ∃ steps b, steps ≤ bodyBudget a rows C ∧
--         Eval (body accepted) steps a (Counters.incrementResult cursorPorts b) ∧
--         b.stacks 859 = a.stacks 859 ∧ b.stacks 860 = a.stacks 860 ∧
--         b.stacks 861 = [] ∧ P b
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.StagedGate.stackMap` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.CounterForPrograms.Data` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport.words` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Counters.incrementResult` (definitions bundle `OAIQ081S114` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.Data` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.Code` (definitions bundle `OAIQ081S128` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.cursorPorts` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.body` (definitions bundle `OAIQ081S151` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.bodyBudget` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.gateValue` (definitions bundle `OAIQ081S165` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.head_multiply_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadSumProgram.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.body_eval)

import Mathlib
import Definitions.Def_OAIQ081S165

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram

open OAI BitProgram StructuredCalls CounterPrograms

open HeadEvaluationProgram.StagedGate (copy copyState clear clearState )

open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
open OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing TruncatedRingProgram

open OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport
open OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram

theorem body_eval (accepted : Code) (a : Data) (rows : List (List (List Bool)))
    (C : ℕ) (P : Data → Prop)
    (hclean : ∀ i : Fin 32, a.stacks (HeadEvaluationProgram.StagedGate.stackMap i) = [])
    (hmatrix : a.stacks 865 = words (rows.map words))
    (hlen : ∀ row ∈ rows, row.length = (a.stacks 859).length)
    (hE : (a.stacks 859).length = (a.stacks 867).length)
    (hH : (a.stacks 859).length = (a.stacks 868).length)
    (hs : a.stacks 861 = [])
    (haccepted : gateValue a rows = true → ∀ out : Fin 40 → Bool, out 15 = true →
      ∃ nb b, nb ≤ C ∧ Eval accepted nb ⟨out, a.stacks⟩ b ∧
        b.stacks 859 = a.stacks 859 ∧ b.stacks 860 = a.stacks 860 ∧
        b.stacks 861 = [] ∧ P b)
    (hrejected : gateValue a rows = false → ∀ out : Fin 40 → Bool, P ⟨out, a.stacks⟩) :
    ∃ steps b, steps ≤ bodyBudget a rows C ∧
      Eval (body accepted) steps a (Counters.incrementResult cursorPorts b) ∧
      b.stacks 859 = a.stacks 859 ∧ b.stacks 860 = a.stacks 860 ∧
      b.stacks 861 = [] ∧ P b := by
  sorry

open scoped BigOperators

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram
end
