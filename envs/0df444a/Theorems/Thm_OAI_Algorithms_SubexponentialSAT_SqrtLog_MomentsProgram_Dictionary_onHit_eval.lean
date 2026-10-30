-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_MomentsProgram_Dictionary_onHit_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.onHit_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:11:37.712909+00:00
-- url     : https://prove2.me/theorems/f38222de-0d30-4082-ac2b-e37cfc74e6ec
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.onHit_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.onHit_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/MomentsProgramDictionaryHit.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/MomentsProgramDictionaryHit.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines`, `open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing`):
--
--   ```lean
--   theorem onHit_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
--       (pairs : List (Word (baseWidth p t) × Word (baseWidth p t)))
--       (regs : Fin 8 → Bool) (a : Tape)
--       (hm : a.modulus = M.bits) (hnew : a.coeff = RingScan.leftBits pairs)
--       (hf : a.found = Encoding.frame (RingScan.rightBits pairs))
--       (hl : a.left = []) (hr : a.right = []) (ho : a.out = []) (hs : a.steps = [])
--       (hc : a.count.length = pairs.length) (hw : a.width.length = baseWidth p t) :
--       ∃ n ≤ hitBudget p t pairs, ∃ rr,
--         Eval onHit n (machine regs a)
--           (machine rr { a with found := [], left := [], right := [], steps := [], out := RingScan.sumBits p t M pairs })
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.Tape` (definitions bundle `OAIQ081S016` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.leftBits`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.rightBits` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScan.sumBits` (definitions bundle `OAIQ081S049` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.hitBudget` (definitions bundle `OAIQ081S077` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.onHit` (definitions bundle `OAIQ081S084` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.machine` (definitions bundle `OAIQ081S110` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.frame` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.insert_hit_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.fetchAdd_code` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/MomentsProgramDictionaryHit.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.onHit_eval)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S110

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem onHit_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (pairs : List (Word (baseWidth p t) × Word (baseWidth p t)))
    (regs : Fin 8 → Bool) (a : Tape)
    (hm : a.modulus = M.bits) (hnew : a.coeff = RingScan.leftBits pairs)
    (hf : a.found = Encoding.frame (RingScan.rightBits pairs))
    (hl : a.left = []) (hr : a.right = []) (ho : a.out = []) (hs : a.steps = [])
    (hc : a.count.length = pairs.length) (hw : a.width.length = baseWidth p t) :
    ∃ n ≤ hitBudget p t pairs, ∃ rr,
      Eval onHit n (machine regs a)
        (machine rr { a with found := [], left := [], right := [], steps := [], out := RingScan.sumBits p t M pairs }) := by
  sorry

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

end OAI.Algorithms
end
