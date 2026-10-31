-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutSourceRowsProgram_sourceRows_relSpec
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_relSpec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:00:27.822172+00:00
-- url     : https://prove2.me/theorems/3224f1f0-6df3-446a-9e8a-bfc212985283
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_relSpec: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_relSpec` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutSourceRowsProgramRowsModel.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutSourceRowsProgramRowsModel.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram`, with `open SubexponentialSAT BitProgram StructuredCalls`, `open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing`):
--
--   ```lean
--   theorem sourceRows_relSpec (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
--       (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
--       (cache : RingProgram.ScalarCache 3 t) (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
--       (D : ℕ) (width : List Bool) (frame : Fin 6 → List Bool)
--       (source : Code) (base : Store) (I K L N : ℕ) (ps : List (ℕ × ℕ))
--       (value : ℕ → ℕ → Polynomial (a.O t))
--       (spec : ∀ j, j < N → ∀ remaining acc,
--         RelSourceSpec source (rowState base j remaining acc)
--           (fun e : Algorithm.Expr (List (PolynomialExecutorProgram.Coeff (baseWidth 3 t) d)) =>
--             SubexpPostfixControl.serializeCode DensePolynomialProgram.encode e.compile)
--           (TypedSourceRel DensePolynomialProgram.encode
--             (PolynomialExecutorProgram.meaning (RingProgram.modelRing t ht hd a M cache)) (value j) L) I K L)
--       (hs : base 337=LayoutOwnerFiberProgram.stream ps)
--       (howner : ∀ i : Fin 11, 2 ≤ i.val → base (ownerStacks i)=[])
--       (hwork : RowWorkClean base)
--       (hI : ∀ j, j < N → ∀ i∈LayoutOwnerFiberProgram.fiberIndices j 0 ps, i ≤ I)
--       (H : PolynomialExecutorProgram.Ready 3 t M cache (RingProgram.modelProgram t a M cache)
--         (HornerProgram.modelTable t a M cache) D width frame
--           (executionContext (evaluationInput base))) :
--       RelRowSpec (sourceRowWith source) base DensePolynomialProgram.encode
--         (fun j out => PolynomialExecutorProgram.meaning (RingProgram.modelRing t ht hd a M cache) out=
--           Truncation.trunc D (ownerSum ps j (value j))) N
--         (uniformRowBudget N ps I K L D d (baseWidth 3 t) (base 21).length (base 26).length)
--         (D*(d*baseWidth 3 t))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.Algorithm.Expr` and `OAI.Algorithms.SubexponentialSAT.Algorithm.Expr.compile` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.fiberIndices` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.Truncation.trunc` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.RowWorkClean`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.Store`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.evaluationInput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.ownerStacks` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.rowState` (definitions bundle `OAIQ081S014` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPostfixControl.serializeCode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.TypedSourceRel` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.ownerSum` (definitions bundle `OAIQ081S036` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutOwnerFiberProgram.stream` (definitions bundle `OAIQ081S072` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.executionContext` (definitions bundle `OAIQ081S075` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.uniformRowBudget` (definitions bundle `OAIQ081S091` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Coeff`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.encode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.modelProgram` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.modelRing` (definitions bundle `OAIQ081S100` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.modelTable` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.Code`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.RelRowSpec`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.RelSourceSpec`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.Coeff` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.meaning` (definitions bundle `OAIQ081S125` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRowWith` (definitions bundle `OAIQ081S144` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.Ready` (definitions bundle `OAIQ081S151` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutSourceRowsProgramRowsModel.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram.sourceRows_relSpec)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S144
import Definitions.Def_OAIQ081S151

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
attribute [local simp] Fin.coe_ofNat_eq_mod

theorem sourceRows_relSpec (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (a : RingModel.Data d) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (D : ℕ) (width : List Bool) (frame : Fin 6 → List Bool)
    (source : Code) (base : Store) (I K L N : ℕ) (ps : List (ℕ × ℕ))
    (value : ℕ → ℕ → Polynomial (a.O t))
    (spec : ∀ j, j < N → ∀ remaining acc,
      RelSourceSpec source (rowState base j remaining acc)
        (fun e : Algorithm.Expr (List (PolynomialExecutorProgram.Coeff (baseWidth 3 t) d)) =>
          SubexpPostfixControl.serializeCode DensePolynomialProgram.encode e.compile)
        (TypedSourceRel DensePolynomialProgram.encode
          (PolynomialExecutorProgram.meaning (RingProgram.modelRing t ht hd a M cache)) (value j) L) I K L)
    (hs : base 337=LayoutOwnerFiberProgram.stream ps)
    (howner : ∀ i : Fin 11, 2 ≤ i.val → base (ownerStacks i)=[])
    (hwork : RowWorkClean base)
    (hI : ∀ j, j < N → ∀ i∈LayoutOwnerFiberProgram.fiberIndices j 0 ps, i ≤ I)
    (H : PolynomialExecutorProgram.Ready 3 t M cache (RingProgram.modelProgram t a M cache)
      (HornerProgram.modelTable t a M cache) D width frame
        (executionContext (evaluationInput base))) :
    RelRowSpec (sourceRowWith source) base DensePolynomialProgram.encode
      (fun j out => PolynomialExecutorProgram.meaning (RingProgram.modelRing t ht hd a M cache) out=
        Truncation.trunc D (ownerSum ps j (value j))) N
      (uniformRowBudget N ps I K L D d (baseWidth 3 t) (base 21).length (base 26).length)
      (D*(d*baseWidth 3 t)) := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
end
