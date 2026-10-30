-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_CodeChecks_local_checker_runs
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.local_checker_runs
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:14:25.31261+00:00
-- url     : https://prove2.me/theorems/abc05cbc-3fd0-4a5e-bf91-a2174f0c1e70
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.local_checker_runs: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.local_checker_runs` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SparseCodeProgram.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SparseCodeProgram.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks`, with `open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram`):
--
--   ```lean
--   theorem local_checker_runs {t D : ℕ} (Q : Fin t → Fin D → SparseCode.F3)
--       (d : ℕ) (a : ScanState) (A : ℕ) (ha : ∀ i, (a.stacks i).length ≤ A)
--       (he : WorkEmpty (projectState id localStreamStacks a))
--       (hm : a.stacks 18 = matrixFrames Q) (ht : a.stacks 19 = List.replicate t true)
--       (hd : a.stacks 20 = List.replicate d true) (hD : a.stacks 21 = List.replicate D true)
--       (hp : a.stacks 22 = []) (htmp : a.stacks 23 = []) (hcounter : a.stacks 24 = [])
--       (hlatch : a.stacks 25 = []) (hscratch : a.stacks 26 = []) (hcopy : a.stacks 27 = []) :
--       ∃ steps out, Eval localChecker steps a out ∧
--         steps ≤ localStreamBudget t D d + 15 * D + 2 * coreSpace A D (callbackBudget t D d) + 18 ∧
--         (out.regs 15 = true ↔ SparseCode.HasDistance Q d) ∧ out.stacks = a.stacks ∧
--         (∀ prefixSteps intermediate, prefixSteps ≤ steps →
--           Trace (compiled localChecker 21 25) prefixSteps
--             (a.withPC (some (compiled localChecker 21 25).entry)) intermediate →
--           ∀ i, (intermediate.stacks i).length ≤
--             40 * A + 15 * D + 43 * coreSpace A D (callbackBudget t D d) + 18)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.F3` (definitions bundle `OAIQ081S005` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.callbackBudget` (definitions bundle `OAIQ081S006` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.coreSpace` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.localStreamStacks` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.projectState` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.localStreamBudget` (definitions bundle `OAIQ081S042` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.matrixFrames` (definitions bundle `OAIQ081S050` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.SparseCode.HasDistance` (definitions bundle `OAIQ081S060` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.ScanState` (definitions bundle `OAIQ081S098` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram.WorkEmpty` (definitions bundle `OAIQ081S102` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.localChecker` (definitions bundle `OAIQ081S114` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SparseCodeSearch.local_search_runs` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/SparseCodeProgram.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks.local_checker_runs)

import Mathlib
import Definitions.Def_OAIQ081S102
import Definitions.Def_OAIQ081S114

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgram

theorem local_checker_runs {t D : ℕ} (Q : Fin t → Fin D → SparseCode.F3)
    (d : ℕ) (a : ScanState) (A : ℕ) (ha : ∀ i, (a.stacks i).length ≤ A)
    (he : WorkEmpty (projectState id localStreamStacks a))
    (hm : a.stacks 18 = matrixFrames Q) (ht : a.stacks 19 = List.replicate t true)
    (hd : a.stacks 20 = List.replicate d true) (hD : a.stacks 21 = List.replicate D true)
    (hp : a.stacks 22 = []) (htmp : a.stacks 23 = []) (hcounter : a.stacks 24 = [])
    (hlatch : a.stacks 25 = []) (hscratch : a.stacks 26 = []) (hcopy : a.stacks 27 = []) :
    ∃ steps out, Eval localChecker steps a out ∧
      steps ≤ localStreamBudget t D d + 15 * D + 2 * coreSpace A D (callbackBudget t D d) + 18 ∧
      (out.regs 15 = true ↔ SparseCode.HasDistance Q d) ∧ out.stacks = a.stacks ∧
      (∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace (compiled localChecker 21 25) prefixSteps
          (a.withPC (some (compiled localChecker 21 25).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          40 * A + 15 * D + 43 * coreSpace A D (callbackBudget t D d) + 18) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CodeChecks
end
