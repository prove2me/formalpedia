-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafQueryFrontend_rawCommand_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.rawCommand_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:34:06.09595+00:00
-- url     : https://prove2.me/theorems/8139c273-fc92-470b-ae84-d039e3e4718a
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.rawCommand_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.rawCommand_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafQueryFrontendRawRun.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafQueryFrontendRawRun.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend`, with `open SubexponentialSAT BitProgram StructuredCalls`):
--
--   ```lean
--   theorem rawCommand_eval (a : Data) (he : emptyRange a 500 580)
--       (ht : a.stacks 679=[]) (hout : a.stacks 718=[])
--       (b : ℕ) (hb : 0 < b) (clauses : List (List Bool))
--       (codes : Fin clauses.length → List ℕ)
--       (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
--       (rows : HashScopeProgram.RawTable.Rows clauses.length) (hbound : 3*clauses.length ≤ 2^b)
--       (mark : Option (Fin clauses.length)) (index width modulus : List Bool)
--       (hindex : ∀ i, mark=some i → index=Encoding.encodeNat i.val)
--       (hw : width.length=b) (hm : BinaryArithmetic.toNat modulus=clauses.length)
--       (h700 : a.stacks 700=Encoding.encodeList id clauses)
--       (h701 : a.stacks 701=HashScopeProgram.RawTable.inputBits b rows)
--       (h705 : a.stacks 705=index) (h706 : a.stacks 706=[mark.isSome])
--       (h707 : a.stacks 707=modulus) (h708 : a.stacks 708=width) :
--       ∃ n c, Eval rawCommand n a c ∧
--         c.stacks 718=LeafStatisticsProgram.scopeBits (HashScopeProgram.Complete.scopes 1 0 codes rows mark) ∧
--         n ≤ copiesCost scopeCopies a+21+
--           HashScopeProgram.Complete.cost 1 0 b modulus clauses codes rows mark index+
--           7*(LeafStatisticsProgram.scopeBits (HashScopeProgram.Complete.scopes 1 0 codes rows mark)).length ∧
--         (∀ i : Fin 768, (i.val < 500 ∨ 580 ≤ i.val) → i≠718 → c.stacks i=a.stacks i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable.Rows` (definitions bundle `OAIQ081S008` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.scopeCopies` (definitions bundle `OAIQ081S017` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable.inputBits` (definitions bundle `OAIQ081S031` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.scopeBits` (definitions bundle `OAIQ081S059` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Data` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.emptyRange` (definitions bundle `OAIQ081S093` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.copiesCost` (definitions bundle `OAIQ081S110` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Complete.cost` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Complete.scopes` (definitions bundle `OAIQ081S119` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.rawCommand` (definitions bundle `OAIQ081S130` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat`, `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` and `OAI.Algorithms.SubexponentialSAT.Encoding.encodeNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.coreCommand_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.coreCommand_eval_bounded` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafQueryFrontendRawRun.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.rawCommand_eval)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S119
import Definitions.Def_OAIQ081S130

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem rawCommand_eval (a : Data) (he : emptyRange a 500 580)
    (ht : a.stacks 679=[]) (hout : a.stacks 718=[])
    (b : ℕ) (hb : 0 < b) (clauses : List (List Bool))
    (codes : Fin clauses.length → List ℕ)
    (hc : ∀ i, clauses[i.val]=Encoding.encodeList Encoding.encodeNat (codes i))
    (rows : HashScopeProgram.RawTable.Rows clauses.length) (hbound : 3*clauses.length ≤ 2^b)
    (mark : Option (Fin clauses.length)) (index width modulus : List Bool)
    (hindex : ∀ i, mark=some i → index=Encoding.encodeNat i.val)
    (hw : width.length=b) (hm : BinaryArithmetic.toNat modulus=clauses.length)
    (h700 : a.stacks 700=Encoding.encodeList id clauses)
    (h701 : a.stacks 701=HashScopeProgram.RawTable.inputBits b rows)
    (h705 : a.stacks 705=index) (h706 : a.stacks 706=[mark.isSome])
    (h707 : a.stacks 707=modulus) (h708 : a.stacks 708=width) :
    ∃ n c, Eval rawCommand n a c ∧
      c.stacks 718=LeafStatisticsProgram.scopeBits (HashScopeProgram.Complete.scopes 1 0 codes rows mark) ∧
      n ≤ copiesCost scopeCopies a+21+
        HashScopeProgram.Complete.cost 1 0 b modulus clauses codes rows mark index+
        7*(LeafStatisticsProgram.scopeBits (HashScopeProgram.Complete.scopes 1 0 codes rows mark)).length ∧
      (∀ i : Fin 768, (i.val < 500 ∨ 580 ≤ i.val) → i≠718 → c.stacks i=a.stacks i) := by
  sorry

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end
