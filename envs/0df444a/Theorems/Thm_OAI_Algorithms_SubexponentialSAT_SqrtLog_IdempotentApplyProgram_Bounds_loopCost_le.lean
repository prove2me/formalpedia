-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_IdempotentApplyProgram_Bounds_loopCost_le
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.loopCost_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:53:19.888203+00:00
-- url     : https://prove2.me/theorems/d5f5ceac-dd3e-4cbc-9e99-069142dc4f1c
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.loopCost_le: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.loopCost_le` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentApplyProgramBounds.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentApplyProgramBounds.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds`, with `open SubexpLiftRing SubexpQuarticRing`, `open MomentsProgram`, `open Steps`):
--
--   ```lean
--   theorem loopCost_le (ctx : Context p t n d) (vars : Finset (Fin n))
--       (hu : 0 < ctx.u) (hJ : 0 < ctx.J) (h g : Stored p t (n:=n) (d:=d))
--       (hh : Bounded ctx vars h) (hg : Bounded ctx vars g)
--       (vs : List (Triple (RingProgram.ScalarCode p t))) (a : Stored p t (n:=n) (d:=d))
--       (ha : Bounded ctx vars a) :
--       loopCost ctx h g vs a ≤
--         loopEnvelope (baseWidth p t) d n ctx.u ctx.J (capacity vars ctx.u ctx.J) vs.length
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Triple` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.capacity` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.loopEnvelope` (definitions bundle `OAIQ081S032` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Stored`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.Bounded`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.Context` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.loopCost` (definitions bundle `OAIQ081S139` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.totalCost_le` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentApplyProgramBounds.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds.loopCost_le)

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
open Steps

variable {p t n d : ℕ} [Fact p.Prime]

theorem loopCost_le (ctx : Context p t n d) (vars : Finset (Fin n))
    (hu : 0 < ctx.u) (hJ : 0 < ctx.J) (h g : Stored p t (n:=n) (d:=d))
    (hh : Bounded ctx vars h) (hg : Bounded ctx vars g)
    (vs : List (Triple (RingProgram.ScalarCode p t))) (a : Stored p t (n:=n) (d:=d))
    (ha : Bounded ctx vars a) :
    loopCost ctx h g vs a ≤
      loopEnvelope (baseWidth p t) d n ctx.u ctx.J (capacity vars ctx.u ctx.J) vs.length := by
  sorry

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Bounds

end OAI.Algorithms
end
