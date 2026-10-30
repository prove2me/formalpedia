-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HeadSumSpace_scan_resources
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumSpace.scan_resources
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T01:37:09.050878+00:00
-- url     : https://prove2.me/theorems/09252f83-fd6d-4b32-8d77-229197ef54e8
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumSpace.scan_resources: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumSpace.scan_resources` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadSumSpace.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadSumSpace.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumSpace`, with `open BitProgram StructuredCalls CounterPrograms CounterForPrograms`, `open HeadEvaluationProgram.StagedGate`):
--
--   ```lean
--   theorem scan_resources (accepted : HeadSumProgram.Code)
--       (I : ℕ → HeadSumProgram.Data → Prop)
--       (h bound cost : ℕ)
--       (hcursorI : ∀ i d, I i d → HeadSumProgram.Cursor h i d)
--       (hbound : ∀ i d, I i d → ∀ j, (d.stacks j).length ≤ bound)
--       (hbudget : 9 * (h + 1) + 8 ≤ bound)
--       (spec : ∀ i d, I i d → d.stacks 861 = [] → 0 < value (d.stacks 860) →
--         ∃ nb e, nb ≤ cost ∧ Eval (HeadSumProgram.body accepted) nb d e ∧
--           e.stacks 860 = d.stacks 860 ∧ e.stacks 861 = [] ∧
--           I (i + 1) (nextState HeadSumProgram.fuelPorts e))
--       (hcallback : ∀ i d e nb, I i d → d.stacks 861 = [] →
--         0 < value (d.stacks 860) → Eval (HeadSumProgram.body accepted) nb d e →
--         ∀ q z, q ≤ nb → Trace (compiled (HeadSumProgram.body accepted) 860 860) q
--           (d.withPC (some (compiled (HeadSumProgram.body accepted) 860 860).entry)) z →
--           ∀ j, (z.stacks j).length ≤ bound)
--       (a : HeadSumProgram.Data) (hshape : a.stacks 651 = List.replicate h false)
--       (hcursor : a.stacks 859 = []) (hfuel : a.stacks 860 = [])
--       (hscratch : a.stacks 861 = []) (htemp : a.stacks 31 = [])
--       (hframe : ∀ j, (a.stacks j).length ≤ bound)
--       (hi : I 0 (testResult HeadSumProgram.fuelPorts (HeadSumProgram.seeded a))) :
--       ∃ steps e,
--         Trace (HeadSumProgram.scanProgram accepted) steps
--           (a.withPC (some (HeadSumProgram.scanProgram accepted).entry))
--           ((HeadSumProgram.finalized e).withPC none) ∧
--         I (2 ^ h) e ∧
--         (HeadSumProgram.finalized e).stacks 853 = e.stacks 853 ∧
--         (HeadSumProgram.finalized e).stacks 859 = [] ∧
--         (HeadSumProgram.finalized e).stacks 860 = [] ∧
--         (HeadSumProgram.finalized e).stacks 861 = [] ∧
--         steps ≤ (2 ^ h + 1) * (cost + 16 * (h + 1) + 17) + 2 * bound + 22 * h + 30 ∧
--         ∀ q z, q ≤ steps → Trace (HeadSumProgram.scanProgram accepted) q
--           (a.withPC (some (HeadSumProgram.scanProgram accepted).entry)) z →
--           ∀ j, (z.stacks j).length ≤ bound
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.CounterPrograms.value` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.CounterForPrograms.nextState` and `OAI.Algorithms.SubexponentialSAT.CounterForPrograms.testResult` (definitions bundle `OAIQ081S045` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.Data` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.Code` (definitions bundle `OAIQ081S128` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.fuelPorts` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.body`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.scan` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.scanProgram` (definitions bundle `OAIQ081S151` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.Cursor`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.finalized` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.seeded` (definitions bundle `OAIQ081S165` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadAcceptedSpace.head_resources_of_local_time` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/HeadSumSpace.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumSpace.scan_resources)

import Mathlib
import Definitions.Def_OAIQ081S165

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumSpace

open BitProgram StructuredCalls CounterPrograms CounterForPrograms

open HeadEvaluationProgram.StagedGate

theorem scan_resources (accepted : HeadSumProgram.Code)
    (I : ℕ → HeadSumProgram.Data → Prop)
    (h bound cost : ℕ)
    (hcursorI : ∀ i d, I i d → HeadSumProgram.Cursor h i d)
    (hbound : ∀ i d, I i d → ∀ j, (d.stacks j).length ≤ bound)
    (hbudget : 9 * (h + 1) + 8 ≤ bound)
    (spec : ∀ i d, I i d → d.stacks 861 = [] → 0 < value (d.stacks 860) →
      ∃ nb e, nb ≤ cost ∧ Eval (HeadSumProgram.body accepted) nb d e ∧
        e.stacks 860 = d.stacks 860 ∧ e.stacks 861 = [] ∧
        I (i + 1) (nextState HeadSumProgram.fuelPorts e))
    (hcallback : ∀ i d e nb, I i d → d.stacks 861 = [] →
      0 < value (d.stacks 860) → Eval (HeadSumProgram.body accepted) nb d e →
      ∀ q z, q ≤ nb → Trace (compiled (HeadSumProgram.body accepted) 860 860) q
        (d.withPC (some (compiled (HeadSumProgram.body accepted) 860 860).entry)) z →
        ∀ j, (z.stacks j).length ≤ bound)
    (a : HeadSumProgram.Data) (hshape : a.stacks 651 = List.replicate h false)
    (hcursor : a.stacks 859 = []) (hfuel : a.stacks 860 = [])
    (hscratch : a.stacks 861 = []) (htemp : a.stacks 31 = [])
    (hframe : ∀ j, (a.stacks j).length ≤ bound)
    (hi : I 0 (testResult HeadSumProgram.fuelPorts (HeadSumProgram.seeded a))) :
    ∃ steps e,
      Trace (HeadSumProgram.scanProgram accepted) steps
        (a.withPC (some (HeadSumProgram.scanProgram accepted).entry))
        ((HeadSumProgram.finalized e).withPC none) ∧
      I (2 ^ h) e ∧
      (HeadSumProgram.finalized e).stacks 853 = e.stacks 853 ∧
      (HeadSumProgram.finalized e).stacks 859 = [] ∧
      (HeadSumProgram.finalized e).stacks 860 = [] ∧
      (HeadSumProgram.finalized e).stacks 861 = [] ∧
      steps ≤ (2 ^ h + 1) * (cost + 16 * (h + 1) + 17) + 2 * bound + 22 * h + 30 ∧
      ∀ q z, q ≤ steps → Trace (HeadSumProgram.scanProgram accepted) q
        (a.withPC (some (HeadSumProgram.scanProgram accepted).entry)) z →
        ∀ j, (z.stacks j).length ≤ bound := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumSpace
end
