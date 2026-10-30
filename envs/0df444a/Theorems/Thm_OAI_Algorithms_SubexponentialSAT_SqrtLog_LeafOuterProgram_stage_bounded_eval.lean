-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafOuterProgram_stage_bounded_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.stage_bounded_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:10:44.421603+00:00
-- url     : https://prove2.me/theorems/aeef2b84-a749-4f9c-953f-f098f28baacf
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.stage_bounded_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.stage_bounded_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafOuterProgramStage.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafOuterProgramStage.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram`, with `open SubexponentialSAT BitProgram StructuredCalls`, `open SubexpSetupStorage`):
--
--   ```lean
--   theorem stage_bounded_eval {r s l : ℕ} (inputs outputs : List Route)
--       (p : Program r s l) (register : Fin r → Fin 40) (stack : Fin s → Fin 896)
--       (hr : Function.Injective register) (hs : Function.Injective stack)
--       (hwork : ∀ i, stack i ≠ 767)
--       (hi : ∀ q ∈ inputs, routeValid q) (ho : ∀ q ∈ outputs, routeValid q)
--       (hli : inputs.length ≤ 32) (hlo : outputs.length ≤ 32)
--       (a : Data) (B : ℕ) (hb : WordBound B a) (ht : a.stacks 767 = [])
--       (out : State r s) (budget : ℕ)
--       (run : RunsIn p budget
--         ((projectState register stack (routesState inputs a)).withPC (some p.entry))
--         (out.withPC none)) :
--       ∃ n ≤ 10000*(B+budget+1),
--         Eval (stage inputs p register stack outputs) n a
--           (stageResult inputs outputs register stack a out)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.Route` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.routeValid` (definitions bundle `OAIQ081S015` of this split); `OAI.Algorithms.SubexponentialSAT.BitProgram.RunsIn` and `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.projectState` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.stage` (definitions bundle `OAIQ081S058` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.routesState` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.stageResult` (definitions bundle `OAIQ081S092` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.WordBound` (definitions bundle `OAIQ081S106` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCodeAssembly.afterMetadata_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeafSetup.parameters_trace_space` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafOuterProgramStage.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.stage_bounded_eval)

import Mathlib
import Definitions.Def_OAIQ081S092
import Definitions.Def_OAIQ081S106

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafOuterProgram

open SubexponentialSAT BitProgram StructuredCalls
open SubexpSetupStorage

theorem stage_bounded_eval {r s l : ℕ} (inputs outputs : List Route)
    (p : Program r s l) (register : Fin r → Fin 40) (stack : Fin s → Fin 896)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (hwork : ∀ i, stack i ≠ 767)
    (hi : ∀ q ∈ inputs, routeValid q) (ho : ∀ q ∈ outputs, routeValid q)
    (hli : inputs.length ≤ 32) (hlo : outputs.length ≤ 32)
    (a : Data) (B : ℕ) (hb : WordBound B a) (ht : a.stacks 767 = [])
    (out : State r s) (budget : ℕ)
    (run : RunsIn p budget
      ((projectState register stack (routesState inputs a)).withPC (some p.entry))
      (out.withPC none)) :
    ∃ n ≤ 10000*(B+budget+1),
      Eval (stage inputs p register stack outputs) n a
        (stageResult inputs outputs register stack a out) := by
  sorry

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
end
