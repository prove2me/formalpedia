-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_RawShuffle_fourTensorKernel_cancellation
-- name    : OAI.ElementaryPositivity.RawShuffle.fourTensorKernel_cancellation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T18:31:19.49393+00:00
-- url     : https://prove2.me/theorems/e6e501c1-b9b2-4171-a69a-38e4051f0429
-- title:
--   OAI.ElementaryPositivity.RawShuffle.fourTensorKernel_cancellation: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.RawShuffle.fourTensorKernel_cancellation` of [lean/OAI/Combinatorics/Chromatic/Shuffle/FourTensorKernel.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/FourTensorKernel.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.RawShuffle`, with `open MvPolynomial HahnSeries`, `open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.RectangularKernel`, `open scoped TensorProduct`):
--
--   ```lean
--   lemma fourTensorKernel_cancellation (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
--       (A : Cut d₁ e₁) (B : Cut d₂ e₂) :
--       (fourRowsInverseUnit a d₁ e₁ d₂ e₂ A B).val *
--         ((fourRowsInverseUnit (fun _ _ : I=>0) d₁ e₁ d₂ e₂ A B)⁻¹).val *
--         polynomial (fourRelativeTaylor d₁ e₁ d₂ e₂ (fourCrossTensor a d₁ e₁ d₂ e₂))=
--       (((-1 : (LaurentSeries ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)))ˣ)^eulerForm a d₂ e₁) *
--         (fourFirstInverseUnit a d₁ e₁ d₂ e₂ *
--           fourSecondInverseUnit a d₁ e₁ d₂ e₂ *
--           (fourCrossingInverseUnit a d₁ e₁ d₂ e₂ *
--           (fourCrossingInverseUnit (fun i j=>a j i) d₁ e₁ d₂ e₂)⁻¹))).val
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElementaryPositivity.LaurentAtInfinity.polynomial`, `OAI.ElementaryPositivity.RawShuffle.Cut`, `OAI.ElementaryPositivity.RawShuffle.S`, `OAI.ElementaryPositivity.RawShuffle.eulerForm` and `OAI.ElementaryPositivity.RawShuffle.symmetricSpace` (definitions bundle `OAIQ368Chrom017` of this split); `OAI.ElementaryPositivity.RawShuffle.cancelFourNonUnital`, `OAI.ElementaryPositivity.RawShuffle.cancelFourRing`, `OAI.ElementaryPositivity.RawShuffle.cancelTensorAlg` and `OAI.ElementaryPositivity.RawShuffle.cancelTensorRing` (definitions bundle `OAIQ368Chrom022` of this split); `OAI.ElementaryPositivity.RawShuffle.fourCrossTensor` (definitions bundle `OAIQ368Chrom027` of this split); `OAI.ElementaryPositivity.RawShuffle.fourCrossingInverseUnit`, `OAI.ElementaryPositivity.RawShuffle.fourFirstInverseUnit`, `OAI.ElementaryPositivity.RawShuffle.fourRelativeTaylor`, `OAI.ElementaryPositivity.RawShuffle.fourRowsInverseUnit`, `OAI.ElementaryPositivity.RawShuffle.fourSecondInverseUnit`, `OAI.ElementaryPositivity.RawShuffle.taylorFourAlgebra` and `OAI.ElementaryPositivity.RawShuffle.taylorTensorAlgebra` (definitions bundle `OAIQ368Chrom033` of this split).
--
--   **Used by.** The proof of `OAI.ElementaryPositivity.RawShuffle.cellTransfer_normalized` of this split imports it.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/FourTensorKernel.lean (declaration OAI.ElementaryPositivity.RawShuffle.fourTensorKernel_cancellation)

import Mathlib
import Definitions.Def_OAIQ368Chrom027
import Definitions.Def_OAIQ368Chrom033

section

attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instOne _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instOne _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
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
lemma fourTensorKernel_cancellation (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (A : Cut d₁ e₁) (B : Cut d₂ e₂) :
    (fourRowsInverseUnit a d₁ e₁ d₂ e₂ A B).val *
      ((fourRowsInverseUnit (fun _ _ : I=>0) d₁ e₁ d₂ e₂ A B)⁻¹).val *
      polynomial (fourRelativeTaylor d₁ e₁ d₂ e₂ (fourCrossTensor a d₁ e₁ d₂ e₂))=
    (((-1 : (LaurentSeries ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)))ˣ)^eulerForm a d₂ e₁) *
      (fourFirstInverseUnit a d₁ e₁ d₂ e₂ *
        fourSecondInverseUnit a d₁ e₁ d₂ e₂ *
        (fourCrossingInverseUnit a d₁ e₁ d₂ e₂ *
        (fourCrossingInverseUnit (fun i j=>a j i) d₁ e₁ d₂ e₂)⁻¹))).val := by
  sorry

end ElementaryPositivity.RawShuffle

end

end OAI
end
