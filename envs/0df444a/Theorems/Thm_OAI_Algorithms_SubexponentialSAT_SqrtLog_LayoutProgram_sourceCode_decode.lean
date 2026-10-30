-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_sourceCode_decode
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.sourceCode_decode
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:53:01.764629+00:00
-- url     : https://prove2.me/theorems/a8218530-7a00-4a67-ae02-3c9401f63abb
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.sourceCode_decode: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.sourceCode_decode` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramRowCode.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramRowCode.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram`, with `open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpRowInterpolation`, `open SubexponentialSAT.SubexpRepresentedRows SubexponentialSAT.SubexpTaylorExecution`, `open LayoutScaledMatrices`):
--
--   ```lean
--   theorem sourceCode_decode (cache : NodeCache C Q) {node : Fin Q → O}
--       (units : NodeUnits node)
--       (hnode : ∀ t, ops.decode (cache.node t) = node t)
--       (hnodeInv : ∀ t, ops.decode (cache.inverse t) = units.nodeInverse t)
--       (hdiff : ∀ t s, ops.decode (cache.difference t s) = units.differenceInverse t s)
--       (A R : ℕ) (u : UniversalType r Q Δ) (i : Fin Δ)
--       (y : UniversalType r Q Δ) :
--       (mapCode ops.decode (sourceCode ops.program cache integerWord inverseDenominator A R u i y)).denote =
--         sourceRow (LayoutNumerator.family r Q Δ A R) denominator u i R units y
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RepresentedRing` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpRowInterpolation.NodeUnits`, `OAI.Algorithms.SubexponentialSAT.SubexpRowInterpolation.NodeUnits.differenceInverse` and `OAI.Algorithms.SubexponentialSAT.SubexpRowInterpolation.NodeUnits.nodeInverse` (definitions bundle `OAIQ081S011` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpRepresentedRows.NodeCache` (definitions bundle `OAIQ081S013` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RepresentedRing.program` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpTaylorExecution.mapCode` and `OAI.Algorithms.SubexponentialSAT.SubexpRowInterpolation.PolynomialCode.denote` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator.family` (definitions bundle `OAIQ081S055` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.sourceCode` (definitions bundle `OAIQ081S058` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutScaledMatrices.sourceRow` (definitions bundle `OAIQ081S072` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceTyped.row_meaning` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramRowCode.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.sourceCode_decode)

import Mathlib
import Definitions.Def_OAIQ081S043
import Definitions.Def_OAIQ081S058
import Definitions.Def_OAIQ081S072

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpRowInterpolation
open SubexponentialSAT.SubexpRepresentedRows SubexponentialSAT.SubexpTaylorExecution
open LayoutScaledMatrices

variable {C O : Type*} {r Q Δ : ℕ}

variable [CommRing O] (ops : RepresentedRing C O)
variable (integerWord : ℤ → C) (hinteger : ∀ z, ops.decode (integerWord z) = (z : O))
variable (denominator : Oˣ) (inverseDenominator : C)
variable (hinverse : ops.decode inverseDenominator = (↑(denominator⁻¹) : O))

include hinteger hinverse in
theorem sourceCode_decode (cache : NodeCache C Q) {node : Fin Q → O}
    (units : NodeUnits node)
    (hnode : ∀ t, ops.decode (cache.node t) = node t)
    (hnodeInv : ∀ t, ops.decode (cache.inverse t) = units.nodeInverse t)
    (hdiff : ∀ t s, ops.decode (cache.difference t s) = units.differenceInverse t s)
    (A R : ℕ) (u : UniversalType r Q Δ) (i : Fin Δ)
    (y : UniversalType r Q Δ) :
    (mapCode ops.decode (sourceCode ops.program cache integerWord inverseDenominator A R u i y)).denote =
      sourceRow (LayoutNumerator.family r Q Δ A R) denominator u i R units y := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
end
