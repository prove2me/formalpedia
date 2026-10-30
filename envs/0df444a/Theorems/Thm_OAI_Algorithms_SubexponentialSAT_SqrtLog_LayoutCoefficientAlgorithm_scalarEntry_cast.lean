-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutCoefficientAlgorithm_scalarEntry_cast
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm.scalarEntry_cast
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:47:08.134807+00:00
-- url     : https://prove2.me/theorems/efc86d91-fbac-43b0-9ae6-72ba46be18b3
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm.scalarEntry_cast: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm.scalarEntry_cast` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutCoefficientAlgorithmEntry.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutCoefficientAlgorithmEntry.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm`, with `open scoped BigOperators`, `open SubexponentialSAT.MulticolorTypes SubexponentialSAT.BinomialInterpolation`, `open SubexponentialSAT.Subexp.MatrixEntryKernel SubexponentialSAT.Subexp.MatrixSupport`):
--
--   ```lean
--   theorem scalarEntry_cast (i : Fin Δ) (t : Fin Q) (A R : ℕ)
--       (u y : UniversalType r Q Δ) :
--       (scalarEntry i t A R u y : ℚ) =
--         (LayoutNumerator.denominator R : ℚ) * matrixEntry i t R
--           (fun j => (coefficientAt A R j : ℚ)) u y
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm.coefficientAt` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator.denominator` (definitions bundle `OAIQ081S012` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm.scalarEntry` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixSupport.matrixEntry` (definitions bundle `OAIQ081S055` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.paddedConstraint_cover`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.paddedConstraint_shape` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.sourceCode_decode` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutCoefficientAlgorithmEntry.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm.scalarEntry_cast)

import Mathlib
import Definitions.Def_OAIQ081S055

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm

open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.BinomialInterpolation
open SubexponentialSAT.Subexp.MatrixEntryKernel SubexponentialSAT.Subexp.MatrixSupport

variable {r Q Δ : ℕ}

theorem scalarEntry_cast (i : Fin Δ) (t : Fin Q) (A R : ℕ)
    (u y : UniversalType r Q Δ) :
    (scalarEntry i t A R u y : ℚ) =
      (LayoutNumerator.denominator R : ℚ) * matrixEntry i t R
        (fun j => (coefficientAt A R j : ℚ)) u y := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm

end OAI.Algorithms
end
