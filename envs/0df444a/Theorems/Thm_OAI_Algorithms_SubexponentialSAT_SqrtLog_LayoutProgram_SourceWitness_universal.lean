-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_SourceWitness_universal
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceWitness.universal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:45:54.860321+00:00
-- url     : https://prove2.me/theorems/fa4fcfaa-fc60-41f4-92d9-936ea2c2155c
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceWitness.universal: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceWitness.universal` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramSourceWitness.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramSourceWitness.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceWitness`, with `open SubexponentialSAT.Subexp SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.MulticolorTypes`, `open SubexponentialSAT.SubexpRepresentedRows SubexponentialSAT.SubexpRowInterpolation`, `open PolynomialExecutorProgram`):
--
--   ```lean
--   theorem universal (ops : RepresentedRing (Coeff B d) O) (hB : 0 < B)
--       (cache : NodeCache (Coeff B d) Q)
--       (integerWord : ℤ → Coeff B d) (hinteger : ∀ z,ops.decode (integerWord z)=(z:O))
--       (denom : Oˣ) (invDenom : Coeff B d) (hinv : ops.decode invDenom=(↑(denom⁻¹):O))
--       {node : Fin Q → O} (units : NodeUnits node)
--       (hnode : ∀ i,ops.decode (cache.node i)=node i)
--       (hni : ∀ i,ops.decode (cache.inverse i)=units.nodeInverse i)
--       (hdi : ∀ i j,ops.decode (cache.difference i j)=units.differenceInverse i j)
--       (values inverse negative : Fin Q → Coeff B d) (difference : Fin Q → Fin Q → Coeff B d)
--       (A R : ℕ) (u y : UniversalType r Q 1) (delta : Coeff B d) (limit : List Bool)
--       (hv : ∀ i,ops.decode (values i)=ops.decode (sourceValue ops.program integerWord invDenom A R u 0 y i))
--       (hi : ∀ i,ops.decode (inverse i)=ops.decode (cache.inverse i))
--       (hn : ∀ i,ops.decode (negative i)=ops.decode ((ops.negRun (cache.node i)).1))
--       (hdiff : ∀ i j,ops.decode (difference i j)=ops.decode (cache.difference i j))
--       (hdelta : ops.decode delta=ops.decode (if u=y then ops.oneRun.1 else ops.zeroRun.1))
--       (hlimit : limit.length=R)
--       (width rowWidth : List Bool) (hw : width.length=d*B) (hrw : rowWidth.length=Q*width.length)
--       (S : ℕ) (hQ : Q ≤ S) (hW : width.length ≤ S) (hRW : rowWidth.length ≤ S) (hR : R ≤ S) :
--       Generated ops R (UniversalRowSourceBound.sourceLengthBound S)
--         (LayoutScaledMatrices.sourceRow (LayoutNumerator.family r Q 1 A R) denom u 0 R units y)
--         (UniversalRowProgram.rowCode (RingProgram.flat ops.zeroRun.1) (RingProgram.flat ops.oneRun.1)
--           (RingProgram.flat ops.zeroRun.1++RingProgram.flat ops.oneRun.1)
--           (UniversalRowDataProgram.row (SourceTyped.tables RingProgram.flat values inverse negative difference)
--             (UniversalRowTableSource.positions (mismatchPositions (fun v=>v.head) (u.slot 0) y))
--             (RingProgram.flat delta) limit))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RepresentedRing` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpRowInterpolation.NodeUnits`, `OAI.Algorithms.SubexponentialSAT.SubexpRowInterpolation.mismatchPositions`, `OAI.Algorithms.SubexponentialSAT.SubexpRowInterpolation.NodeUnits.differenceInverse` and `OAI.Algorithms.SubexponentialSAT.SubexpRowInterpolation.NodeUnits.nodeInverse` (definitions bundle `OAIQ081S011` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpRepresentedRows.NodeCache` (definitions bundle `OAIQ081S013` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowSourceBound.sourceLengthBound` (definitions bundle `OAIQ081S014` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RepresentedRing.program` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowDataProgram.row` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped.tables` (definitions bundle `OAIQ081S036` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowTableSource.positions` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.flat` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator.family` (definitions bundle `OAIQ081S055` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.sourceValue` (definitions bundle `OAIQ081S058` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutScaledMatrices.sourceRow` (definitions bundle `OAIQ081S072` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.Coeff` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceWitness.Generated` (definitions bundle `OAIQ081S125` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowProgram.rowCode` (definitions bundle `OAIQ081S186` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.universal_generated` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramSourceWitness.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceWitness.universal)

import Mathlib
import Definitions.Def_OAIQ081S186

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceWitness
open SubexponentialSAT.Subexp SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.SubexpRepresentedRows SubexponentialSAT.SubexpRowInterpolation
open PolynomialExecutorProgram

variable {B d r Q : ℕ} {O : Type*} [CommRing O]

theorem universal (ops : RepresentedRing (Coeff B d) O) (hB : 0 < B)
    (cache : NodeCache (Coeff B d) Q)
    (integerWord : ℤ → Coeff B d) (hinteger : ∀ z,ops.decode (integerWord z)=(z:O))
    (denom : Oˣ) (invDenom : Coeff B d) (hinv : ops.decode invDenom=(↑(denom⁻¹):O))
    {node : Fin Q → O} (units : NodeUnits node)
    (hnode : ∀ i,ops.decode (cache.node i)=node i)
    (hni : ∀ i,ops.decode (cache.inverse i)=units.nodeInverse i)
    (hdi : ∀ i j,ops.decode (cache.difference i j)=units.differenceInverse i j)
    (values inverse negative : Fin Q → Coeff B d) (difference : Fin Q → Fin Q → Coeff B d)
    (A R : ℕ) (u y : UniversalType r Q 1) (delta : Coeff B d) (limit : List Bool)
    (hv : ∀ i,ops.decode (values i)=ops.decode (sourceValue ops.program integerWord invDenom A R u 0 y i))
    (hi : ∀ i,ops.decode (inverse i)=ops.decode (cache.inverse i))
    (hn : ∀ i,ops.decode (negative i)=ops.decode ((ops.negRun (cache.node i)).1))
    (hdiff : ∀ i j,ops.decode (difference i j)=ops.decode (cache.difference i j))
    (hdelta : ops.decode delta=ops.decode (if u=y then ops.oneRun.1 else ops.zeroRun.1))
    (hlimit : limit.length=R)
    (width rowWidth : List Bool) (hw : width.length=d*B) (hrw : rowWidth.length=Q*width.length)
    (S : ℕ) (hQ : Q ≤ S) (hW : width.length ≤ S) (hRW : rowWidth.length ≤ S) (hR : R ≤ S) :
    Generated ops R (UniversalRowSourceBound.sourceLengthBound S)
      (LayoutScaledMatrices.sourceRow (LayoutNumerator.family r Q 1 A R) denom u 0 R units y)
      (UniversalRowProgram.rowCode (RingProgram.flat ops.zeroRun.1) (RingProgram.flat ops.oneRun.1)
        (RingProgram.flat ops.zeroRun.1++RingProgram.flat ops.oneRun.1)
        (UniversalRowDataProgram.row (SourceTyped.tables RingProgram.flat values inverse negative difference)
          (UniversalRowTableSource.positions (mismatchPositions (fun v=>v.head) (u.slot 0) y))
          (RingProgram.flat delta) limit)) := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceWitness

end OAI.Algorithms
end
