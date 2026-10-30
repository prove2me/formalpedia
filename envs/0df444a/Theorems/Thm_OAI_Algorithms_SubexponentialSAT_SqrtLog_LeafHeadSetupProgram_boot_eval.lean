-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafHeadSetupProgram_boot_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.boot_eval
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T01:46:15.483966+00:00
-- url     : https://prove2.me/theorems/d8172d50-b85c-4654-ad8d-4dc71d7f2c0a
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.boot_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.boot_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafHeadSetupProgramBootRun.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafHeadSetupProgramBootRun.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls`):
--
--   ```lean
--   theorem boot_eval (a : Data) (r t : ℕ) (records : List (List Bool))
--       (height R width : List Bool)
--       (hr : a.stacks 130=List.replicate r true) (ht : a.stacks 307=List.replicate t true)
--       (hrecords : a.stacks 136=SubexponentialSAT.Encoding.encodeList id records)
--       (hheight : a.stacks 139=height) (hR : a.stacks 138=R) (hwidth : a.stacks 140=width)
--       (hw : 1+2*height.length*R.length ≤ width.length) :
--       ∃ ra rd rc words steps, steps ≤ bootCost a ra rd rc r t records height R width words ∧
--         Eval boot steps a (bootState a ra rd rc r t records height R width words) ∧
--         words.length=R.length ∧ (∀ w∈words,w.length=width.length) ∧
--         words.map SubexponentialSAT.BinaryArithmetic.toNat=
--           (List.range R.length).map (LayoutCoefficientRecurrence.H height.length)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence.H` (definitions bundle `OAIQ081S011` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Data` (definitions bundle `OAIQ081S090` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.boot` (definitions bundle `OAIQ081S158` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.bootCost` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.bootState` (definitions bundle `OAIQ081S168` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` and `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.bootstrap_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafHeadSetupProgramBootRun.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.boot_eval)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S168

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

noncomputable section
namespace SubexponentialSAT.SqrtLog
namespace LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem boot_eval (a : Data) (r t : ℕ) (records : List (List Bool))
    (height R width : List Bool)
    (hr : a.stacks 130=List.replicate r true) (ht : a.stacks 307=List.replicate t true)
    (hrecords : a.stacks 136=SubexponentialSAT.Encoding.encodeList id records)
    (hheight : a.stacks 139=height) (hR : a.stacks 138=R) (hwidth : a.stacks 140=width)
    (hw : 1+2*height.length*R.length ≤ width.length) :
    ∃ ra rd rc words steps, steps ≤ bootCost a ra rd rc r t records height R width words ∧
      Eval boot steps a (bootState a ra rd rc r t records height R width words) ∧
      words.length=R.length ∧ (∀ w∈words,w.length=width.length) ∧
      words.map SubexponentialSAT.BinaryArithmetic.toNat=
        (List.range R.length).map (LayoutCoefficientRecurrence.H height.length) := by
  sorry

end LeafHeadSetupProgram

end SqrtLog

end SubexponentialSAT

end

end OAI.Algorithms
end
