-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_MomentsProgram_Product_keyPhase_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.keyPhase_eval
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T00:12:16.371581+00:00
-- url     : https://prove2.me/theorems/7049702a-e408-405e-aba0-b797e4a9c84b
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.keyPhase_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.keyPhase_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/MomentsProgramProduct.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/MomentsProgramProduct.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines`):
--
--   ```lean
--   theorem keyPhase_eval {n : ℕ} (left : Squarefree.Index (Fin n)) (u J : ℕ)
--       (entries : List (Squarefree.KeyMapProgram.Entry n)) (regs : Fin 8 → Bool) (a : Store)
--       (hl : a.key = (Squarefree.encodeIndex left).reverse)
--       (hu : a.uCap = List.replicate u true) (hj : a.zCap = List.replicate J true)
--       (hs : a.scaled = Squarefree.Program.rawEntries (Squarefree.KeyMapProgram.encoded entries))
--       (h0 : a.keySource = []) (h1 : a.keyLeft = []) (h2 : a.keyUCap = [])
--       (h3 : a.keyZCap = []) (h4 : a.mapped = []) :
--       ∃ k ≤ 9*a.scaled.length+5*a.key.length+9*a.uCap.length+9*a.zCap.length+
--         Squarefree.KeyMapProgram.budget left u J entries+32, ∃ rr,
--         Eval keyPhase k (state regs a)
--           (state rr {a with scaled := [], key := [], mapped := Squarefree.Program.rawEntries (Squarefree.KeyMapProgram.encoded (Squarefree.KeyMapProgram.mapped left u J entries).reverse)})
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Index` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.Store` (definitions bundle `OAIQ081S008` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.encodeIndex`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram.Entry`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram.mapped` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Program.rawEntries` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram.encoded` (definitions bundle `OAIQ081S063` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.keyPhase` (definitions bundle `OAIQ081S069` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.state` (definitions bundle `OAIQ081S106` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.step_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/MomentsProgramProduct.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.keyPhase_eval)

import Mathlib
import Definitions.Def_OAIQ081S063
import Definitions.Def_OAIQ081S106

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem keyPhase_eval {n : ℕ} (left : Squarefree.Index (Fin n)) (u J : ℕ)
    (entries : List (Squarefree.KeyMapProgram.Entry n)) (regs : Fin 8 → Bool) (a : Store)
    (hl : a.key = (Squarefree.encodeIndex left).reverse)
    (hu : a.uCap = List.replicate u true) (hj : a.zCap = List.replicate J true)
    (hs : a.scaled = Squarefree.Program.rawEntries (Squarefree.KeyMapProgram.encoded entries))
    (h0 : a.keySource = []) (h1 : a.keyLeft = []) (h2 : a.keyUCap = [])
    (h3 : a.keyZCap = []) (h4 : a.mapped = []) :
    ∃ k ≤ 9*a.scaled.length+5*a.key.length+9*a.uCap.length+9*a.zCap.length+
      Squarefree.KeyMapProgram.budget left u J entries+32, ∃ rr,
      Eval keyPhase k (state regs a)
        (state rr {a with scaled := [], key := [], mapped := Squarefree.Program.rawEntries (Squarefree.KeyMapProgram.encoded (Squarefree.KeyMapProgram.mapped left u J entries).reverse)}) := by
  sorry

end SubexponentialSAT.SqrtLog.MomentsProgram.Product

end OAI.Algorithms
end
