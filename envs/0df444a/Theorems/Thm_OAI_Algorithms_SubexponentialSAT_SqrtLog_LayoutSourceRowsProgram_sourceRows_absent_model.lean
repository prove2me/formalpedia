-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram_sourceRows_absent_model
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_absent_model
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T00:59:48.960595+00:00
-- url     : https://prove2.me/theorems/fe35f87a-ea8f-470f-83cd-a289711cec4e
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_absent_model: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_absent_model` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutSourceRowsProgramAbsent.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutSourceRowsProgramAbsent.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram`, with `open SubexponentialSAT BitProgram StructuredCalls`, `open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing`):
--
--   ```lean
--   theorem sourceRows_absent_model (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
--       (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
--       (cache : RingProgram.ScalarCache 3 t) (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
--       (source : Code) (s : Store) (D v N f : ℕ) (ps : List (ℕ × ℕ))
--       (hinit : LayoutSourceRowsProgramInitialize.Ready (s ∘ initializationPorts) D (d*baseWidth 3 t))
--       (hv : s 233=LayoutSourcePlanLookup.unary v)
--       (hN : s 212=LayoutSourcePlanLookup.unary N)
--       (hf : s 216=LayoutSourcePlanLookup.unary f)
--       (hplan : s 337=LayoutOwnerFiberProgram.stream ps)
--       (hmem : (v,N+f) ∉ ps)
--       (hlookup : LayoutSourcePlanLookup.Native.Clean
--         (⟨fun _ => false,initializeFinish s D (d*baseWidth 3 t)⟩ : Data))
--       (hclean : RowsClean (preparedSourceStore s D (d*baseWidth 3 t) ps v N f))
--       (regs : Fin 16 → Bool) :
--       ∃ rows n rf,
--         RowProperty DensePolynomialProgram.encode
--           (fun _ out => PolynomialExecutorProgram.meaning (RingProgram.modelRing t ht hd a M cache) out=0)
--           (D*(d*baseWidth 3 t)) 0 rows ∧ rows.length=N ∧
--         n ≤ LayoutSourceRowsProgramInitialize.budget D (d*baseWidth 3 t)+
--           LayoutSourcePlanLookup.pairBudget v N f ps+N*(26*(D*(d*baseWidth 3 t))+44)+
--           2*(ps.idxOf (v,N+f))+23 ∧
--         Eval (sourceRowsWith source) n (⟨regs,s⟩ : Data)
--           (⟨rf,Function.update (initializeFinish s D (d*baseWidth 3 t)) 205
--             (Encoding.encodeList DensePolynomialProgram.encode rows)⟩ : Data)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.unary`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.RowProperty`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.RowsClean`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.Store`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.initializationPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.initializeFinish`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.preparedSourceStore` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramInitialize.budget` (definitions bundle `OAIQ081S014` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramInitialize.Ready` (definitions bundle `OAIQ081S058` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.stream` (definitions bundle `OAIQ081S072` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.pairBudget` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourcePlanLookup.Native.Clean` (definitions bundle `OAIQ081S091` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Coeff`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.encode` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.modelRing` (definitions bundle `OAIQ081S100` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.Code` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.meaning` (definitions bundle `OAIQ081S125` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRowsWith` (definitions bundle `OAIQ081S144` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` and `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutSourceRowsProgramAbsent.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_absent_model)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S144

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem sourceRows_absent_model (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (source : Code) (s : Store) (D v N f : ℕ) (ps : List (ℕ × ℕ))
    (hinit : LayoutSourceRowsProgramInitialize.Ready (s ∘ initializationPorts) D (d*baseWidth 3 t))
    (hv : s 233=LayoutSourcePlanLookup.unary v)
    (hN : s 212=LayoutSourcePlanLookup.unary N)
    (hf : s 216=LayoutSourcePlanLookup.unary f)
    (hplan : s 337=LayoutOwnerFiberProgram.stream ps)
    (hmem : (v,N+f) ∉ ps)
    (hlookup : LayoutSourcePlanLookup.Native.Clean
      (⟨fun _ => false,initializeFinish s D (d*baseWidth 3 t)⟩ : Data))
    (hclean : RowsClean (preparedSourceStore s D (d*baseWidth 3 t) ps v N f))
    (regs : Fin 16 → Bool) :
    ∃ rows n rf,
      RowProperty DensePolynomialProgram.encode
        (fun _ out => PolynomialExecutorProgram.meaning (RingProgram.modelRing t ht hd a M cache) out=0)
        (D*(d*baseWidth 3 t)) 0 rows ∧ rows.length=N ∧
      n ≤ LayoutSourceRowsProgramInitialize.budget D (d*baseWidth 3 t)+
        LayoutSourcePlanLookup.pairBudget v N f ps+N*(26*(D*(d*baseWidth 3 t))+44)+
        2*(ps.idxOf (v,N+f))+23 ∧
      Eval (sourceRowsWith source) n (⟨regs,s⟩ : Data)
        (⟨rf,Function.update (initializeFinish s D (d*baseWidth 3 t)) 205
          (Encoding.encodeList DensePolynomialProgram.encode rows)⟩ : Data) := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end
