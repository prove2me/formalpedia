-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_RawShuffle_fourSeriesValue_kernelRHS_val
-- name    : OAI.ElementaryPositivity.RawShuffle.fourSeriesValue_kernelRHS_val
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T18:26:49.295206+00:00
-- url     : https://prove2.me/theorems/2058059a-61fe-4e73-829f-65569750ff2c
-- title:
--   OAI.ElementaryPositivity.RawShuffle.fourSeriesValue_kernelRHS_val: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.RawShuffle.fourSeriesValue_kernelRHS_val` of [lean/OAI/Combinatorics/Chromatic/Shuffle/FourTensorKernel.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/FourTensorKernel.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.RawShuffle`, with `open MvPolynomial HahnSeries`, `open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.RectangularKernel`, `open scoped TensorProduct`):
--
--   ```lean
--   lemma fourSeriesValue_kernelRHS_val (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
--       fourSeriesValue d₁ e₁ d₂ e₂ (fourTensorKernelRHS a d₁ e₁ d₂ e₂).val=
--       (fourTotalInverseUnit a d₁ e₁ d₂ e₂ * (fourClearingUnit d₁ e₁ d₂ e₂)⁻¹ *
--         fourCrossAffineUnit a d₁ e₁ d₂ e₂).val
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElementaryPositivity.RawShuffle.CellVars`, `OAI.ElementaryPositivity.RawShuffle.S` and `OAI.ElementaryPositivity.RawShuffle.symmetricSpace` (definitions bundle `OAIQ368Chrom017` of this split); `OAI.ElementaryPositivity.RawShuffle.cancelTensorAlg`, `OAI.ElementaryPositivity.RawShuffle.cancelTensorDistrib` and `OAI.ElementaryPositivity.RawShuffle.cancelTensorRing` (definitions bundle `OAIQ368Chrom022` of this split); `OAI.ElementaryPositivity.RawShuffle.fourClearingUnit`, `OAI.ElementaryPositivity.RawShuffle.fourCrossAffineUnit`, `OAI.ElementaryPositivity.RawShuffle.fourSeriesValue`, `OAI.ElementaryPositivity.RawShuffle.fourTensorKernelRHS` and `OAI.ElementaryPositivity.RawShuffle.fourTotalInverseUnit` (definitions bundle `OAIQ368Chrom033` of this split).
--
--   **Used by.** The proof of `OAI.ElementaryPositivity.RawShuffle.fourTensorKernel_cancellation` of this split imports it.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/FourTensorKernel.lean (declaration OAI.ElementaryPositivity.RawShuffle.fourSeriesValue_kernelRHS_val)

import Mathlib
import Definitions.Def_OAIQ368Chrom033

section

attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial HahnSeries
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.RectangularKernel
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cancelTensorRing
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cancelTensorDistrib
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cancelTensorAlg
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cancelFourRing
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cancelFourAlg
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cancelTensorSelf
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cancelTensorNonUnital
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cancelFourNonUnital
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cancelSeriesRing
lemma fourSeriesValue_kernelRHS_val (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    fourSeriesValue d₁ e₁ d₂ e₂ (fourTensorKernelRHS a d₁ e₁ d₂ e₂).val=
    (fourTotalInverseUnit a d₁ e₁ d₂ e₂ * (fourClearingUnit d₁ e₁ d₂ e₂)⁻¹ *
      fourCrossAffineUnit a d₁ e₁ d₂ e₂).val := by
  sorry

end ElementaryPositivity.RawShuffle

end

end OAI
end
