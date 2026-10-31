-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HashInputProgram_Expansion_forward_original_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Expansion.forward_original_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:53:32.319552+00:00
-- url     : https://prove2.me/theorems/d6a2f11e-e8da-4579-8df9-05997c14a74a
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Expansion.forward_original_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Expansion.forward_original_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HashInputProgramExpansion.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HashInputProgramExpansion.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Expansion`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls`, `open HashCircuitProgram.Native`):
--
--   ```lean
--   theorem forward_original_eval {n : ℕ} (t D : ℕ) (ht : 0 < t) (hD : 0 < D)
--       (b : ℕ) (hb : 0 < b) (source : List (List (SAT.Literal (Fin n))))
--       (terms : List (Fin (encodedClauses source).length × ZMod 3))
--       (hbound : 3*(encodedClauses source).length ≤ 2^b) (a : LeafProgram.Expansion.Data)
--       (hraw : a.stacks 154=(Loop.rawInput b terms).reverse)
--       (hsource : a.stacks 700=ExecQuantitativeSparsify.encodeRawFormula source)
--       (hwidth : (a.stacks 708).length=b)
--       (hmodulus : BinaryArithmetic.toNat (a.stacks 707)=(encodedClauses source).length)
--       (hshape : (a.stacks 280).length=D*SubexpLiftRing.baseWidth 3 t)
--       (houtput : a.stacks 64=[])
--       (hwork : ∀ i∈LeafProgram.Expansion.scratch,a.stacks i=[])
--       (h358 : a.stacks 358=[]) (h359 : a.stacks 359=[]) :
--       ∃ k rf, k ≤ 9*(a.stacks 154).length+7+
--           Loop.uniformBudget t (D-1) b (a.stacks 707) (encodedClauses source) terms.length+3 ∧
--         Eval LeafProgram.Expansion.forwardCommand k a
--           (LeafProgram.Expansion.finished (LeafProgram.Expansion.reversedInput a) rf
--             (Encoding.encodeList id ((weightedRow t D source terms).map Row.payload)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Expansion.scratch` (definitions bundle `OAIQ081S015` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.ExecQuantitativeSparsify.encodeRawFormula` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.rawInput` (definitions bundle `OAIQ081S031` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Expansion.encodedClauses` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.uniformBudget` (definitions bundle `OAIQ081S051` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Expansion.Data` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Expansion.reversedInput` (definitions bundle `OAIQ081S093` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Expansion.finished` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Expansion.forwardCommand` (definitions bundle `OAIQ081S109` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Expansion.weightedRow`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.WeightedClause` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.payload` (definitions bundle `OAIQ081S139` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat`, `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` and `OAI.Algorithms.SubexponentialSAT.SAT.Literal` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.expanded_hash_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HashInputProgramExpansion.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Expansion.forward_original_eval)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S109
import Definitions.Def_OAIQ081S139

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashInputProgram.Expansion
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open HashCircuitProgram.Native
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem forward_original_eval {n : ℕ} (t D : ℕ) (ht : 0 < t) (hD : 0 < D)
    (b : ℕ) (hb : 0 < b) (source : List (List (SAT.Literal (Fin n))))
    (terms : List (Fin (encodedClauses source).length × ZMod 3))
    (hbound : 3*(encodedClauses source).length ≤ 2^b) (a : LeafProgram.Expansion.Data)
    (hraw : a.stacks 154=(Loop.rawInput b terms).reverse)
    (hsource : a.stacks 700=ExecQuantitativeSparsify.encodeRawFormula source)
    (hwidth : (a.stacks 708).length=b)
    (hmodulus : BinaryArithmetic.toNat (a.stacks 707)=(encodedClauses source).length)
    (hshape : (a.stacks 280).length=D*SubexpLiftRing.baseWidth 3 t)
    (houtput : a.stacks 64=[])
    (hwork : ∀ i∈LeafProgram.Expansion.scratch,a.stacks i=[])
    (h358 : a.stacks 358=[]) (h359 : a.stacks 359=[]) :
    ∃ k rf, k ≤ 9*(a.stacks 154).length+7+
        Loop.uniformBudget t (D-1) b (a.stacks 707) (encodedClauses source) terms.length+3 ∧
      Eval LeafProgram.Expansion.forwardCommand k a
        (LeafProgram.Expansion.finished (LeafProgram.Expansion.reversedInput a) rf
          (Encoding.encodeList id ((weightedRow t D source terms).map Row.payload))) := by
  sorry

end SubexponentialSAT.SqrtLog.HashInputProgram.Expansion

end OAI.Algorithms
end
