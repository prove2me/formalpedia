-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryNodeFinish_command_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish.command_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:18:21.762692+00:00
-- url     : https://prove2.me/theorems/08b590a6-e19f-49d3-932b-67fbd7ffdca7
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish.command_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish.command_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryNodeFinish.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryNodeFinish.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish`, with `open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing`, `open MomentsProgram TruncatedRingProgram`):
--
--   ```lean
--   theorem command_eval (p t : ℕ) [Fact p.Prime]
--       (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
--       {n d u J : ℕ} (entries : List (Product.Entry n (baseWidth p t) d))
--       (he : Good ∅ u J entries) (zero : RingProgram.Code (Word (baseWidth p t)) d)
--       (width degree marker taylor shape : List Bool)
--       (hd : degree.length = d) (hw : width.length = baseWidth p t)
--       (hu : marker.length = u) (hJ : taylor.length = J) (hs : shape.length = n)
--       (a : Data) (incoming : ℕ) (ha : ∀ i, (a.stacks i).length ≤ incoming)
--       (hr : NodeAppendSpace.MasterReady a M.bits width degree (Product.bytes entries)
--         (RingProgram.flat zero) marker taylor shape)
--       (hout : (a.stacks 863).length + J * (d * baseWidth p t) ≤ incoming)
--       (hx : (a.stacks 307).length + 1 ≤ incoming) :
--       let bits := MomentsReadoutProgram.outputBits p t M cache entries u zero 0 J
--       ∃ steps rr,
--         steps + 1 ≤ budget n (baseWidth p t) d u J incoming ∧
--         Eval command steps a
--           (result a rr M.bits width degree (Product.bytes entries) (RingProgram.flat zero)
--             marker taylor shape bits) ∧
--         bits.length = J * (d * baseWidth p t) ∧
--         (∀ i, ((result a rr M.bits width degree (Product.bytes entries) (RingProgram.flat zero)
--           marker taylor shape bits).stacks i).length ≤ incoming)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.flat` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish.budget` (definitions bundle `OAIQ081S064` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish.Data` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.Entry` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.bytes` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.outputBits` (definitions bundle `OAIQ081S130` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram.Good` (definitions bundle `OAIQ081S151` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeAppendSpace.MasterReady` (definitions bundle `OAIQ081S165` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish.result` (definitions bundle `OAIQ081S172` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish.command` (definitions bundle `OAIQ081S178` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeReadout.run_common` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryNodeFinish.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish.command_eval)

import Mathlib
import Definitions.Def_OAIQ081S178

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

theorem command_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d u J : ℕ} (entries : List (Product.Entry n (baseWidth p t) d))
    (he : Good ∅ u J entries) (zero : RingProgram.Code (Word (baseWidth p t)) d)
    (width degree marker taylor shape : List Bool)
    (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (hu : marker.length = u) (hJ : taylor.length = J) (hs : shape.length = n)
    (a : Data) (incoming : ℕ) (ha : ∀ i, (a.stacks i).length ≤ incoming)
    (hr : NodeAppendSpace.MasterReady a M.bits width degree (Product.bytes entries)
      (RingProgram.flat zero) marker taylor shape)
    (hout : (a.stacks 863).length + J * (d * baseWidth p t) ≤ incoming)
    (hx : (a.stacks 307).length + 1 ≤ incoming) :
    let bits := MomentsReadoutProgram.outputBits p t M cache entries u zero 0 J
    ∃ steps rr,
      steps + 1 ≤ budget n (baseWidth p t) d u J incoming ∧
      Eval command steps a
        (result a rr M.bits width degree (Product.bytes entries) (RingProgram.flat zero)
          marker taylor shape bits) ∧
      bits.length = J * (d * baseWidth p t) ∧
      (∀ i, ((result a rr M.bits width degree (Product.bytes entries) (RingProgram.flat zero)
        marker taylor shape bits).stacks i).length ≤ incoming) := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeFinish
end
