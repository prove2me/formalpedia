-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_Squarefree_KeyMapProgram_join_store
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram.join_store
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T00:40:15.192525+00:00
-- url     : https://prove2.me/theorems/0ee4b0eb-b0f0-46e6-951b-caced7216878
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram.join_store: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram.join_store` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/SquarefreeKeyMapProgram.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/SquarefreeKeyMapProgram.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls`):
--
--   ```lean
--   theorem join_store {n : ℕ} (regs : Fin 8 → Bool) (s : Store) (a b : Index (Fin n))
--       (ha : s.leftCopy = encodeIndex a) (hb : s.rightKey = encodeIndex b)
--       (ho : s.joinedRev = []) :
--       ∃ rr, Eval join (4*(a.u+b.u+a.z+b.z)+6*n+22) (state regs s)
--         (state rr {s with leftCopy := [], rightKey := [], joinedRev := (encodeIndex (a.join b)).reverse})
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Index` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Index.join` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram.Store` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.encodeIndex` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram.join` (definitions bundle `OAIQ081S051` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram.state` (definitions bundle `OAIQ081S135` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.shiftU_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.keyPhase_eval` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/SquarefreeKeyMapProgram.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram.join_store)

import Mathlib
import Definitions.Def_OAIQ081S135

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem join_store {n : ℕ} (regs : Fin 8 → Bool) (s : Store) (a b : Index (Fin n))
    (ha : s.leftCopy = encodeIndex a) (hb : s.rightKey = encodeIndex b)
    (ho : s.joinedRev = []) :
    ∃ rr, Eval join (4*(a.u+b.u+a.z+b.z)+6*n+22) (state regs s)
      (state rr {s with leftCopy := [], rightKey := [], joinedRev := (encodeIndex (a.join b)).reverse}) := by
  sorry

end SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram

end OAI.Algorithms
end
