-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HeadAcceptedSpace_head_resources_of_local_time
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedSpace.head_resources_of_local_time
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:35:41.973509+00:00
-- url     : https://prove2.me/theorems/1ee88fa6-70b8-4962-b0b0-019a68e5326f
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedSpace.head_resources_of_local_time: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedSpace.head_resources_of_local_time` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadAcceptedSpace.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadAcceptedSpace.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedSpace`, with `open BitProgram StructuredCalls HighQueryAdapter`, `open CounterPrograms CounterForPrograms`, `open OAI BitProgram StructuredCalls SqrtLog SqrtLog.MomentsProgram`, `open SubexpLiftRing SubexpQuarticRing TruncatedRingProgram HeadSumProgram`):
--
--   ```lean
--   theorem head_resources_of_local_time (accepted : HeadSumProgram.Code)
--       (I : ℕ → HeadSumProgram.Data → Prop)
--       (h inputCap bound cost : ℕ)
--       (hcursorI : ∀ i d, I i d → HeadSumProgram.Cursor h i d)
--       (hcompact : ∀ i d, I i d → ∀ j, (d.stacks j).length ≤ inputCap)
--       (hlocal : 896 * inputCap + cost ≤ bound)
--       (hbudget : 9 * (h + 1) + 8 ≤ bound)
--       (spec : ∀ i d, I i d → d.stacks 861 = [] → 0 < value (d.stacks 860) →
--         ∃ nb e, nb ≤ cost ∧ Eval (HeadSumProgram.body accepted) nb d e ∧
--           e.stacks 860 = d.stacks 860 ∧ e.stacks 861 = [] ∧
--           I (i + 1) (nextState HeadSumProgram.fuelPorts e))
--       (a : HeadSumProgram.Data) (hshape : a.stacks 651 = List.replicate h false)
--       (hframe : ∀ j, (a.stacks j).length ≤ bound)
--       (hi : I 0 (testResult HeadSumProgram.fuelPorts
--         (HeadSumProgram.seeded (HeadSumAssembly.cleared a)))) :
--       ∃ steps e,
--         Trace (HeadSumAssembly.headProgram accepted) steps
--           (a.withPC (some (HeadSumAssembly.headProgram accepted).entry))
--           ((HeadSumProgram.finalized e).withPC none) ∧
--         Eval (HeadSumAssembly.head accepted) (steps - 1) a (HeadSumProgram.finalized e) ∧
--         I (2 ^ h) e ∧
--         (HeadSumProgram.finalized e).stacks 853 = e.stacks 853 ∧
--         (HeadSumProgram.finalized e).stacks 859 = [] ∧
--         (HeadSumProgram.finalized e).stacks 860 = [] ∧
--         (HeadSumProgram.finalized e).stacks 861 = [] ∧
--         steps ≤ (2 * cost + 126 * bound + 54 * h + 286) * 2 ^ h ∧
--         ∀ q z, q ≤ steps → Trace (HeadSumAssembly.headProgram accepted) q
--           (a.withPC (some (HeadSumAssembly.headProgram accepted).entry)) z →
--           ∀ j, (z.stacks j).length ≤ bound
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.CounterPrograms.value` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.CounterForPrograms.nextState` and `OAI.Algorithms.SubexponentialSAT.CounterForPrograms.testResult` (definitions bundle `OAIQ081S045` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.Data` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.Code` (definitions bundle `OAIQ081S128` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.fuelPorts` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumAssembly.head`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumAssembly.headProgram` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.body` (definitions bundle `OAIQ081S151` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumAssembly.cleared`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.Cursor`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.finalized` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.seeded` (definitions bundle `OAIQ081S165` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorHead.head_multiply_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadAcceptedSpace.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedSpace.head_resources_of_local_time)

import Mathlib
import Definitions.Def_OAIQ081S165

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedSpace

open BitProgram StructuredCalls HighQueryAdapter

open CounterPrograms CounterForPrograms

open OAI BitProgram StructuredCalls SqrtLog SqrtLog.MomentsProgram
open SubexpLiftRing SubexpQuarticRing TruncatedRingProgram HeadSumProgram

theorem head_resources_of_local_time (accepted : HeadSumProgram.Code)
    (I : ℕ → HeadSumProgram.Data → Prop)
    (h inputCap bound cost : ℕ)
    (hcursorI : ∀ i d, I i d → HeadSumProgram.Cursor h i d)
    (hcompact : ∀ i d, I i d → ∀ j, (d.stacks j).length ≤ inputCap)
    (hlocal : 896 * inputCap + cost ≤ bound)
    (hbudget : 9 * (h + 1) + 8 ≤ bound)
    (spec : ∀ i d, I i d → d.stacks 861 = [] → 0 < value (d.stacks 860) →
      ∃ nb e, nb ≤ cost ∧ Eval (HeadSumProgram.body accepted) nb d e ∧
        e.stacks 860 = d.stacks 860 ∧ e.stacks 861 = [] ∧
        I (i + 1) (nextState HeadSumProgram.fuelPorts e))
    (a : HeadSumProgram.Data) (hshape : a.stacks 651 = List.replicate h false)
    (hframe : ∀ j, (a.stacks j).length ≤ bound)
    (hi : I 0 (testResult HeadSumProgram.fuelPorts
      (HeadSumProgram.seeded (HeadSumAssembly.cleared a)))) :
    ∃ steps e,
      Trace (HeadSumAssembly.headProgram accepted) steps
        (a.withPC (some (HeadSumAssembly.headProgram accepted).entry))
        ((HeadSumProgram.finalized e).withPC none) ∧
      Eval (HeadSumAssembly.head accepted) (steps - 1) a (HeadSumProgram.finalized e) ∧
      I (2 ^ h) e ∧
      (HeadSumProgram.finalized e).stacks 853 = e.stacks 853 ∧
      (HeadSumProgram.finalized e).stacks 859 = [] ∧
      (HeadSumProgram.finalized e).stacks 860 = [] ∧
      (HeadSumProgram.finalized e).stacks 861 = [] ∧
      steps ≤ (2 * cost + 126 * bound + 54 * h + 286) * 2 ^ h ∧
      ∀ q z, q ≤ steps → Trace (HeadSumAssembly.headProgram accepted) q
        (a.withPC (some (HeadSumAssembly.headProgram accepted).entry)) z →
        ∀ j, (z.stacks j).length ≤ bound := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedSpace
end
