-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_IdempotentApplyProgram_Multiplier_shiftU_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.shiftU_eval
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T00:00:56.650486+00:00
-- url     : https://prove2.me/theorems/90ec81e2-ea06-4479-a892-8c2844b66211
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.shiftU_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.shiftU_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentApplyProgramMultiplierKernel.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentApplyProgramMultiplierKernel.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier`, with `open BitProgram StructuredCalls`, `open HashCircuitProgram.Native`):
--
--   ```lean
--   theorem shiftU_eval {n : ℕ} (a : Squarefree.Index (Fin n)) (u J : ℕ)
--       (entries : List (Squarefree.KeyMapProgram.Entry n)) (x : State 8 96)
--       (hs:x.stacks 67=Squarefree.Program.rawEntries (Squarefree.KeyMapProgram.encoded entries))
--       (hk:x.stacks 94=Squarefree.encodeIndex a)
--       (hu:x.stacks 45=List.replicate u true) (hJ:x.stacks 46=List.replicate J true)
--       (hclean:∀ i ∈ ([80,81,82,83,84,85,89,90,91,92]:List (Fin 96)),x.stacks i=[]) :
--       ∃ k ≤ Squarefree.KeyMapProgram.budget a u J entries+2, ∃ rr,
--         Eval shiftU k x ⟨rr,Function.update (Function.update x.stacks 67 []) 86
--           (Squarefree.Program.rawEntries (Squarefree.KeyMapProgram.encoded (Squarefree.KeyMapProgram.mapped a u J entries).reverse)++x.stacks 86)⟩
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Index` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.encodeIndex`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram.Entry`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram.mapped` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.rawEntries` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram.encoded` (definitions bundle `OAIQ081S063` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.shiftU` (definitions bundle `OAIQ081S085` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Indicator.command_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/IdempotentApplyProgramMultiplierKernel.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.shiftU_eval)

import Mathlib
import Definitions.Def_OAIQ081S063
import Definitions.Def_OAIQ081S085

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier
open BitProgram StructuredCalls
open HashCircuitProgram.Native

theorem shiftU_eval {n : ℕ} (a : Squarefree.Index (Fin n)) (u J : ℕ)
    (entries : List (Squarefree.KeyMapProgram.Entry n)) (x : State 8 96)
    (hs:x.stacks 67=Squarefree.Program.rawEntries (Squarefree.KeyMapProgram.encoded entries))
    (hk:x.stacks 94=Squarefree.encodeIndex a)
    (hu:x.stacks 45=List.replicate u true) (hJ:x.stacks 46=List.replicate J true)
    (hclean:∀ i ∈ ([80,81,82,83,84,85,89,90,91,92]:List (Fin 96)),x.stacks i=[]) :
    ∃ k ≤ Squarefree.KeyMapProgram.budget a u J entries+2, ∃ rr,
      Eval shiftU k x ⟨rr,Function.update (Function.update x.stacks 67 []) 86
        (Squarefree.Program.rawEntries (Squarefree.KeyMapProgram.encoded (Squarefree.KeyMapProgram.mapped a u J entries).reverse)++x.stacks 86)⟩ := by
  sorry

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier

end OAI.Algorithms
end
