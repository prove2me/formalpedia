-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_RawShuffle_fourSeriesValue_second
-- name    : OAI.ElementaryPositivity.RawShuffle.fourSeriesValue_second
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T18:28:00.670536+00:00
-- url     : https://prove2.me/theorems/204232f0-ee89-4d48-9f2d-35602a468e09
-- title:
--   OAI.ElementaryPositivity.RawShuffle.fourSeriesValue_second: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.RawShuffle.fourSeriesValue_second` of [lean/OAI/Combinatorics/Chromatic/Shuffle/FourTensorKernel.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/FourTensorKernel.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.RawShuffle`, with `open MvPolynomial HahnSeries`, `open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.RectangularKernel`, `open scoped TensorProduct`):
--
--   ```lean
--   lemma fourSeriesValue_second (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
--       Units.map (fourSeriesValue d₁ e₁ d₂ e₂).toMonoidHom (fourSecondInverseUnit a d₁ e₁ d₂ e₂)=
--         rectangular (SeparationInfinity.inverseExponent a)
--           (fun i j x y=>fourAffine d₁ e₁ d₂ e₂ i j (.inr x) (.inr y))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElementaryPositivity.RawShuffle.CellVars`, `OAI.ElementaryPositivity.RawShuffle.S` and `OAI.ElementaryPositivity.RawShuffle.symmetricSpace` (definitions bundle `OAIQ368Chrom017` of this split); `OAI.ElementaryPositivity.RawShuffle.SeparationInfinity.inverseExponent` (definitions bundle `OAIQ368Chrom018` of this split); `OAI.ElementaryPositivity.RawShuffle.cancelFourRing`, `OAI.ElementaryPositivity.RawShuffle.cancelTensorDistrib` and `OAI.ElementaryPositivity.RawShuffle.cancelTensorRing` (definitions bundle `OAIQ368Chrom022` of this split); `OAI.ElementaryPositivity.RawShuffle.fourAffine`, `OAI.ElementaryPositivity.RawShuffle.fourSecondInverseUnit`, `OAI.ElementaryPositivity.RawShuffle.fourSeriesValue` and `OAI.ElementaryPositivity.RectangularKernel.rectangular` (definitions bundle `OAIQ368Chrom033` of this split).
--
--   **Used by.** The proof of `OAI.ElementaryPositivity.RawShuffle.fourSeriesValue_kernelRHS_val` of this split imports it.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/FourTensorKernel.lean (declaration OAI.ElementaryPositivity.RawShuffle.fourSeriesValue_second)

import Mathlib
import Definitions.Def_OAIQ368Chrom033

section

attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
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
lemma fourSeriesValue_second (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ) :
    Units.map (fourSeriesValue d₁ e₁ d₂ e₂).toMonoidHom (fourSecondInverseUnit a d₁ e₁ d₂ e₂)=
      rectangular (SeparationInfinity.inverseExponent a)
        (fun i j x y=>fourAffine d₁ e₁ d₂ e₂ i j (.inr x) (.inr y)) := by
  sorry

end ElementaryPositivity.RawShuffle

end

end OAI
end
