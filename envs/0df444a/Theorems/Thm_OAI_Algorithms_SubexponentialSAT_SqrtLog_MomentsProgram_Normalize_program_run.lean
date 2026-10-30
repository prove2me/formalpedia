-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_MomentsProgram_Normalize_program_run
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Normalize.program_run
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T01:04:40.167113+00:00
-- url     : https://prove2.me/theorems/6bdfb6ae-a722-4258-9d25-4afe3f81f56d
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Normalize.program_run: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Normalize.program_run` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/MomentsProgramNormalize.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/MomentsProgramNormalize.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Normalize`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls`, `open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing`):
--
--   ```lean
--   theorem program_run (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
--       (cache : RingProgram.ScalarCache p t) {d : ℕ} (key : K → List Bool) (hk : Function.Injective key)
--       (source seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
--       (regs : Fin 8 → Bool) (width count : List Bool)
--       (hc : count.length = d) (hw : width.length = baseWidth p t) :
--       ∃ rr, RunsIn program (work p t M cache key source seed + 2)
--         ((state regs M.bits width count (bytes key seed) (bytes key source)).withPC (some program.entry))
--         ((state rr M.bits width count (bytes key (run p t M cache source seed)) []).withPC none)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.BitProgram.RunsIn` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Normalize.program` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Normalize.scan` (definitions bundle `OAIQ081S084` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Normalize.bytes` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Normalize.run` (definitions bundle `OAIQ081S119` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Normalize.work` (definitions bundle `OAIQ081S139` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Normalize.state` (definitions bundle `OAIQ081S146` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadSumProgram.accumulate_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler.commitPair_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution.TupleEnd.command_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryProducerSpace.run_space`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.WeightedCore.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.add_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.step_eval` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/MomentsProgramNormalize.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Normalize.program_run)

import Mathlib
import Definitions.Def_OAIQ081S139
import Definitions.Def_OAIQ081S146

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Normalize
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K : Type*} [DecidableEq K]

theorem program_run (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ} (key : K → List Bool) (hk : Function.Injective key)
    (source seed : List (K × RingProgram.Code (Word (baseWidth p t)) d))
    (regs : Fin 8 → Bool) (width count : List Bool)
    (hc : count.length = d) (hw : width.length = baseWidth p t) :
    ∃ rr, RunsIn program (work p t M cache key source seed + 2)
      ((state regs M.bits width count (bytes key seed) (bytes key source)).withPC (some program.entry))
      ((state rr M.bits width count (bytes key (run p t M cache source seed)) []).withPC none) := by
  sorry

end SubexponentialSAT.SqrtLog.MomentsProgram.Normalize

end OAI.Algorithms
end
