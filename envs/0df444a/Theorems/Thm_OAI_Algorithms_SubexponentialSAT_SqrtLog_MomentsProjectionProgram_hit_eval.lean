-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_MomentsProjectionProgram_hit_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProjectionProgram.hit_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:12:44.801439+00:00
-- url     : https://prove2.me/theorems/7bcee2ba-e4d7-425b-816d-988b145f1eb5
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProjectionProgram.hit_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProjectionProgram.hit_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/MomentsProjectionProgramNative.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/MomentsProjectionProgramNative.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProjectionProgram`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls`):
--
--   ```lean
--   theorem hit_eval (regs : Fin 5 → Bool) (a : Tape) (key coeff : List Bool)
--       (hk : a.newkey = key.reverse) (hc : a.coeff = coeff.reverse) (hf : a.framed = []) :
--       ∃ rf, Eval hit (4*key.length+4*coeff.length+13+
--           (3*(Encoding.frame key++Encoding.frame coeff).length+3))
--         (machine regs a)
--         (machine rf {a with newkey:=[],coeff:=[],framed:=[], output:=(Encoding.frame key++Encoding.frame coeff).reverse++a.output})
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProjectionProgram.Tape` (definitions bundle `OAIQ081S016` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProjectionProgram.hit` (definitions bundle `OAIQ081S060` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProjectionProgram.machine` (definitions bundle `OAIQ081S109` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.frame` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HeadEvaluationProgram.Specialization.raw_dictionary_runsIn` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/MomentsProjectionProgramNative.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProjectionProgram.hit_eval)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S109

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProjectionProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem hit_eval (regs : Fin 5 → Bool) (a : Tape) (key coeff : List Bool)
    (hk : a.newkey = key.reverse) (hc : a.coeff = coeff.reverse) (hf : a.framed = []) :
    ∃ rf, Eval hit (4*key.length+4*coeff.length+13+
        (3*(Encoding.frame key++Encoding.frame coeff).length+3))
      (machine regs a)
      (machine rf {a with newkey:=[],coeff:=[],framed:=[], output:=(Encoding.frame key++Encoding.frame coeff).reverse++a.output}) := by
  sorry

end SubexponentialSAT.SqrtLog.MomentsProjectionProgram

end OAI.Algorithms
end
