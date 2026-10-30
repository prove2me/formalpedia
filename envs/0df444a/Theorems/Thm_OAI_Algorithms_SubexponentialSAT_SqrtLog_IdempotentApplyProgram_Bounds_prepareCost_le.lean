-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_IdempotentApplyProgram_Bounds_prepareCost_le
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.prepareCost_le
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T00:54:17.731679+00:00
-- url     : https://prove2.me/theorems/a05db56e-70aa-45fd-b46e-fd84d9586a06
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.prepareCost_le: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.prepareCost_le` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentApplyProgramBoundsMultiplier.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentApplyProgramBoundsMultiplier.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds`, with `open SubexpLiftRing SubexpQuarticRing`, `open MomentsProgram`, `open Steps Multiplier`):
--
--   ```lean
--   theorem prepareCost_le (ctx : Context p t n d) (vars : Finset (Fin n))
--       (minus : RingProgram.Code (Word (baseWidth p t)) d)
--       (h one : Stored p t (n:=n) (d:=d))
--       (hh : Bounded ctx vars h) (ho : Good vars ctx.u ctx.J one) :
--       prepareCost ctx minus h one ≤
--         prepareEnvelope (baseWidth p t) d n ctx.u ctx.J (capacity vars ctx.u ctx.J)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.capacity` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.prepareEnvelope` (definitions bundle `OAIQ081S032` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Stored`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.Bounded`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.Good`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.prepareCost` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.Context` (definitions bundle `OAIQ081S139` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.totalCost_le` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentApplyProgramBoundsMultiplier.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.prepareCost_le)

import Mathlib
import Definitions.Def_OAIQ081S139

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds

open SubexpLiftRing SubexpQuarticRing
open MomentsProgram
open Steps Multiplier

variable {p t n d : ℕ} [Fact p.Prime]

theorem prepareCost_le (ctx : Context p t n d) (vars : Finset (Fin n))
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (h one : Stored p t (n:=n) (d:=d))
    (hh : Bounded ctx vars h) (ho : Good vars ctx.u ctx.J one) :
    prepareCost ctx minus h one ≤
      prepareEnvelope (baseWidth p t) d n ctx.u ctx.J (capacity vars ctx.u ctx.J) := by
  sorry

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds

end OAI.Algorithms
end
