-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutSourceExpression_typed_row_contract
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceExpression.typed_row_contract
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T00:31:39.714055+00:00
-- url     : https://prove2.me/theorems/6f26db46-4f12-49ee-be48-999c85aef7a9
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceExpression.typed_row_contract: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceExpression.typed_row_contract` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutSourceExpression.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutSourceExpression.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceExpression`, with `open SubexponentialSAT SubexponentialSAT.SubexpSymbolicCost`, `open SubexponentialSAT.Subexp.UniversalRowProgram`, `open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpRepresentedRows SubexponentialSAT.SubexpRowInterpolation`, `open PolynomialExecutorProgram`):
--
--   ```lean
--   theorem typed_row_contract (hi : Function.Injective encode)
--       (A R : ℕ) (u y : UniversalType r Q 1) (delta : C) (limit : List Bool)
--       (hlimit : limit.length=R)
--       (hv : ∀ i,ops.decode (values i)=ops.decode
--         (LayoutProgram.sourceValue ops.program integerWord invDenom A R u 0 y i))
--       (hiv : ∀ i,ops.decode (inverse i)=ops.decode (cache.inverse i))
--       (hnv : ∀ i,ops.decode (negative i)=ops.decode ((ops.negRun (cache.node i)).1))
--       (hdv : ∀ i j,ops.decode (difference i j)=ops.decode (cache.difference i j))
--       (hdelta : ops.decode delta=ops.decode (if u=y then ops.oneRun.1 else ops.zeroRun.1)) :
--       let row := LayoutProgram.SourceTyped.row values inverse negative difference
--         (mismatchPositions (fun v => v.head) (u.slot 0) y) delta R
--       let e := sourceExpr ops.program row
--       ((e.map (meaning ops)).eval =
--         LayoutScaledMatrices.sourceRow (LayoutNumerator.family r Q 1 A R) denom u 0 R units y) ∧
--       (((e.map (meaning ops)).eval).natDegree ≤ R) ∧
--       (meaning ops (evaluate ops.program (R+1) e) =
--         LayoutScaledMatrices.sourceRow (LayoutNumerator.family r Q 1 A R) denom u 0 R units y)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.Algorithm.Expr`, `OAI.Algorithms.SubexponentialSAT.Algorithm.Expr.eval` and `OAI.Algorithms.SubexponentialSAT.Algorithm.Expr.map` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RepresentedRing` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpRowInterpolation.NodeUnits`, `OAI.Algorithms.SubexponentialSAT.SubexpRowInterpolation.mismatchPositions`, `OAI.Algorithms.SubexponentialSAT.SubexpRowInterpolation.NodeUnits.differenceInverse` and `OAI.Algorithms.SubexponentialSAT.SubexpRowInterpolation.NodeUnits.nodeInverse` (definitions bundle `OAIQ081S011` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpRepresentedRows.NodeCache`, `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowGather.Word` and `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowLoop.Tables` (definitions bundle `OAIQ081S013` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RepresentedRing.program` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowProgram.Row` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped.row` (definitions bundle `OAIQ081S036` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator.family` (definitions bundle `OAIQ081S055` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.sourceValue` (definitions bundle `OAIQ081S058` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutScaledMatrices.sourceRow` (definitions bundle `OAIQ081S072` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.meaning` (definitions bundle `OAIQ081S125` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.evaluate` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.sourceExpr` (definitions bundle `OAIQ081S136` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceWitness.universal` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutSourceExpression.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceExpression.typed_row_contract)

import Mathlib
import Definitions.Def_OAIQ081S125
import Definitions.Def_OAIQ081S136

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourceExpression

open SubexponentialSAT SubexponentialSAT.SubexpSymbolicCost
open SubexponentialSAT.Subexp.UniversalRowProgram
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpRepresentedRows SubexponentialSAT.SubexpRowInterpolation
open PolynomialExecutorProgram

section TypedRows

variable {C O : Type*} [Nonempty C] [CommRing O] {r Q : ℕ}
    (encode : C → List Bool) (tables : SubexponentialSAT.Subexp.UniversalRowLoop.Tables)
    (values inverse negative : Fin Q → C) (difference : Fin Q → Fin Q → C)
    (hvalues : ∀ i, tables.values.getD i.val []=encode (values i))
    (hinverse : ∀ i, tables.inverses.getD i.val []=encode (inverse i))
    (hnegative : ∀ i, tables.negatives.getD i.val []=encode (negative i))
    (hdifference : ∀ i j, (tables.differences.getD i.val []).getD j.val []=encode (difference i j))
    (ops : RepresentedRing C O) (cache : NodeCache C Q)
    (integerWord : ℤ → C) (hinteger : ∀ z,ops.decode (integerWord z)=(z:O))
    (denom : Oˣ) (invDenom : C) (hinvDenom : ops.decode invDenom=(↑(denom⁻¹):O))
    {node : Fin Q → O} (units : NodeUnits node)
    (hnode : ∀ i,ops.decode (cache.node i)=node i)
    (hnodeInverse : ∀ i,ops.decode (cache.inverse i)=units.nodeInverse i)
    (hdiffInverse : ∀ i j,ops.decode (cache.difference i j)=units.differenceInverse i j)

include hvalues hinverse hnegative hdifference hinteger hinvDenom hnode hnodeInverse hdiffInverse in
theorem typed_row_contract (hi : Function.Injective encode)
    (A R : ℕ) (u y : UniversalType r Q 1) (delta : C) (limit : List Bool)
    (hlimit : limit.length=R)
    (hv : ∀ i,ops.decode (values i)=ops.decode
      (LayoutProgram.sourceValue ops.program integerWord invDenom A R u 0 y i))
    (hiv : ∀ i,ops.decode (inverse i)=ops.decode (cache.inverse i))
    (hnv : ∀ i,ops.decode (negative i)=ops.decode ((ops.negRun (cache.node i)).1))
    (hdv : ∀ i j,ops.decode (difference i j)=ops.decode (cache.difference i j))
    (hdelta : ops.decode delta=ops.decode (if u=y then ops.oneRun.1 else ops.zeroRun.1)) :
    let row := LayoutProgram.SourceTyped.row values inverse negative difference
      (mismatchPositions (fun v => v.head) (u.slot 0) y) delta R
    let e := sourceExpr ops.program row
    ((e.map (meaning ops)).eval =
      LayoutScaledMatrices.sourceRow (LayoutNumerator.family r Q 1 A R) denom u 0 R units y) ∧
    (((e.map (meaning ops)).eval).natDegree ≤ R) ∧
    (meaning ops (evaluate ops.program (R+1) e) =
      LayoutScaledMatrices.sourceRow (LayoutNumerator.family r Q 1 A R) denom u 0 R units y) := by
  sorry

end TypedRows
end SubexponentialSAT.SqrtLog.LayoutSourceExpression

end OAI.Algorithms
end
