-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_DifferencePairsSpace_program_stack_bound
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsSpace.program_stack_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:50:22.729627+00:00
-- url     : https://prove2.me/theorems/b6719b68-1def-4bab-a10a-f8d6e659546c
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsSpace.program_stack_bound: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsSpace.program_stack_bound` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DifferencePairsSpace.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DifferencePairsSpace.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsSpace`, with `open BitProgram StructuredCalls DifferencePairsProgram`):
--
--   ```lean
--   theorem program_stack_bound (p : Ports r s) (callback : Cmd r s) (output : Fin s)
--       (visit : List (Option Bool) → List Bool → List Bool) (I : State r s → Prop)
--       (C N J B D : ℕ)
--       (spec : CallbackSpec p callback output visit C N I)
--       (hcallback : ∀ j pre a b t, pre.length = N →
--         (j + 1) + pre.countP Option.isSome = J → Cursor p 0 (j + 1) pre true a → I a →
--         (∀ i, (a.stacks i).length ≤ B) → Eval callback t (popped p 0 2 a) b →
--         (∀ i, (b.stacks i).length ≤ B) ∧
--         ∀ q z, q ≤ t → Trace (compiled callback (p.stack 0) (p.stack 2)) q
--           ((popped p 0 2 a).withPC
--             (some (compiled callback (p.stack 0) (p.stack 2)).entry)) z →
--           ∀ i, (z.stacks i).length ≤ D)
--       {steps : ℕ} {a b : State r s} (heval : Eval (command p callback) steps a b)
--       (ha : ∀ i, (a.stacks i).length ≤ B) (hIa : I a)
--       (hdepth : a.stacks (p.stack 0) = List.replicate N true)
--       (hbudget : a.stacks (p.stack 1) = List.replicate J true)
--       (houter : a.stacks (p.stack 2) = []) (hinner : a.stacks (p.stack 3) = []) :
--       ∀ q z, q ≤ steps + 1 → Trace (program p callback) q
--         (a.withPC (some (program p callback).entry)) z →
--         ∀ i, (z.stacks i).length ≤ max D (s * B + 13)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram.Ports` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram.CallbackSpec`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram.Cursor`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram.popped` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsProgram.program` (definitions bundle `OAIQ081S064` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryPairEvaluation.run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/DifferencePairsSpace.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsSpace.program_stack_bound)

import Mathlib
import Definitions.Def_OAIQ081S064

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsSpace

open BitProgram StructuredCalls DifferencePairsProgram

variable {r s : ℕ}

theorem program_stack_bound (p : Ports r s) (callback : Cmd r s) (output : Fin s)
    (visit : List (Option Bool) → List Bool → List Bool) (I : State r s → Prop)
    (C N J B D : ℕ)
    (spec : CallbackSpec p callback output visit C N I)
    (hcallback : ∀ j pre a b t, pre.length = N →
      (j + 1) + pre.countP Option.isSome = J → Cursor p 0 (j + 1) pre true a → I a →
      (∀ i, (a.stacks i).length ≤ B) → Eval callback t (popped p 0 2 a) b →
      (∀ i, (b.stacks i).length ≤ B) ∧
      ∀ q z, q ≤ t → Trace (compiled callback (p.stack 0) (p.stack 2)) q
        ((popped p 0 2 a).withPC
          (some (compiled callback (p.stack 0) (p.stack 2)).entry)) z →
        ∀ i, (z.stacks i).length ≤ D)
    {steps : ℕ} {a b : State r s} (heval : Eval (command p callback) steps a b)
    (ha : ∀ i, (a.stacks i).length ≤ B) (hIa : I a)
    (hdepth : a.stacks (p.stack 0) = List.replicate N true)
    (hbudget : a.stacks (p.stack 1) = List.replicate J true)
    (houter : a.stacks (p.stack 2) = []) (hinner : a.stacks (p.stack 3) = []) :
    ∀ q z, q ≤ steps + 1 → Trace (program p callback) q
      (a.withPC (some (program p callback).entry)) z →
      ∀ i, (z.stacks i).length ≤ max D (s * B + 13) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairsSpace
end
