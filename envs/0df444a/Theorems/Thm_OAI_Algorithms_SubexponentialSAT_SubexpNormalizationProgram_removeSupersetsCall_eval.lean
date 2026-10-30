-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SubexpNormalizationProgram_removeSupersetsCall_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.removeSupersetsCall_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:04:54.92999+00:00
-- url     : https://prove2.me/theorems/b6284719-f4cf-400b-ba3d-55cd56e62346
-- title:
--   OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.removeSupersetsCall_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.removeSupersetsCall_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SubexpNormalizationProgram.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SubexpNormalizationProgram.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram`, with `open BitProgram StructuredCalls`):
--
--   ```lean
--   theorem removeSupersetsCall_eval (F : List (List ℕ)) (d : Data)
--       (hsource : d.stacks 13 = formulaCode F) (hready : Ready d) :
--       ∃ n ≤ 1000 * ((formulaCode F).length + 1) ^ 2, ∃ e : Data,
--         Eval removeSupersetsCall n d e ∧ Ready e ∧
--         e.stacks 13 = formulaCode (removeSupersets F)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.formulaCode` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.Data` and `OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.removeSupersets` (definitions bundle `OAIQ081S065` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.Ready` (definitions bundle `OAIQ081S081` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.removeSupersetsCall` (definitions bundle `OAIQ081S082` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.absorb_eval` and `OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.program_runsIn` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SubexpNormalizationProgram.lean (declaration OAI.Algorithms.SubexponentialSAT.SubexpNormalizationProgram.removeSupersetsCall_eval)

import Mathlib
import Definitions.Def_OAIQ081S081
import Definitions.Def_OAIQ081S082

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SubexpNormalizationProgram

open BitProgram StructuredCalls

theorem removeSupersetsCall_eval (F : List (List ℕ)) (d : Data)
    (hsource : d.stacks 13 = formulaCode F) (hready : Ready d) :
    ∃ n ≤ 1000 * ((formulaCode F).length + 1) ^ 2, ∃ e : Data,
      Eval removeSupersetsCall n d e ∧ Ready e ∧
      e.stacks 13 = formulaCode (removeSupersets F) := by
  sorry

end SubexponentialSAT.SubexpNormalizationProgram

end OAI.Algorithms
end
