-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_RawShuffle_unitalSeparationConstant_shuffle_leading_all
-- name    : OAI.ElementaryPositivity.RawShuffle.unitalSeparationConstant_shuffle_leading_all
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T18:28:56.723194+00:00
-- url     : https://prove2.me/theorems/2376a826-d60c-4aed-8a26-e68bb78ddd06
-- title:
--   OAI.ElementaryPositivity.RawShuffle.unitalSeparationConstant_shuffle_leading_all: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.RawShuffle.unitalSeparationConstant_shuffle_leading_all` of [lean/OAI/Combinatorics/Chromatic/Shuffle/DimensionColumnLeading.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/DimensionColumnLeading.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.RawShuffle`, with `open scoped TensorProduct`, `open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.PackConvolution`, `open HahnSeries SeparationInfinity`):
--
--   ```lean
--   lemma unitalSeparationConstant_shuffle_leading_all (a : I → I → ℕ) (c η : I → ℝ)
--       (hc : ∀ i,0 < c i) (θ : ℝ) {d e α β : I → ℕ} (hχ : SlopeEulerSymmetric a c η θ)
--       (h : d+e=α+β) (U V : ℤ) (f : S d) (g : S e)
--       (hf : quotientAlg a (slope c η) d f∈unitalSourceFiltration a c η hc θ d U)
--       (hg : quotientAlg a (slope c η) e g∈unitalSourceFiltration a c η hc θ e V)
--       (hα : OnSlopeOrZero c η θ α) (hβ : OnSlopeOrZero c η θ β)
--       (hd : OnSlopeOrZero c η θ d)
--       {s : Pack (A:=A)} (R : Realization (α+β) s) :
--       (unitalSeparationSeries a c η hc (hα.compatible hβ)
--         (quotientAlg a (slope c η) (α+β) (castS h (shufflePolynomial a f g)))).coeff 0-
--         gridLeadingB a c η hc θ f g (cutRealizationEquiv R (firstCut α β)).val
--           (leftRealization R (firstCut α β)) (rightRealization R (firstCut α β))∈
--       unitalSourceTensorFiltration a c η hc θ α β (U+V+1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElementaryPositivity.PackConvolution.Cut`, `OAI.ElementaryPositivity.PackConvolution.Pack`, `OAI.ElementaryPositivity.PackConvolution.left`, `OAI.ElementaryPositivity.RawShuffle.B`, `OAI.ElementaryPositivity.RawShuffle.Cut`, `OAI.ElementaryPositivity.RawShuffle.Realization`, `OAI.ElementaryPositivity.RawShuffle.S`, `OAI.ElementaryPositivity.RawShuffle.SizedCut`, `OAI.ElementaryPositivity.RawShuffle.castS`, `OAI.ElementaryPositivity.RawShuffle.cutRealizationEquiv`, `OAI.ElementaryPositivity.RawShuffle.destabilizingSpace`, `OAI.ElementaryPositivity.RawShuffle.firstCut`, `OAI.ElementaryPositivity.RawShuffle.quotientAlg`, `OAI.ElementaryPositivity.RawShuffle.quotientAlgebra`, `OAI.ElementaryPositivity.RawShuffle.quotientCommRing`, `OAI.ElementaryPositivity.RawShuffle.shufflePolynomial`, `OAI.ElementaryPositivity.RawShuffle.symmetricSpace` and `OAI.ElementaryPositivity.SlopeArithmetic.slope` (definitions bundle `OAIQ368Chrom017` of this split); `OAI.ElementaryPositivity.SlopeArithmetic.OnSlopeOrZero` (definitions bundle `OAIQ368Chrom021` of this split); `OAI.ElementaryPositivity.RawShuffle.SlopeEulerSymmetric`, `OAI.ElementaryPositivity.RawShuffle.leftRealization` and `OAI.ElementaryPositivity.RawShuffle.rightRealization` (definitions bundle `OAIQ368Chrom022` of this split); `OAI.ElementaryPositivity.RawShuffle.unitalSourceFiltration`, `OAI.ElementaryPositivity.RawShuffle.unitalSourceTensorFiltration`, `OAI.ElementaryPositivity.RawShuffle.SeparationInfinity.unitalSeparationSeries` and `OAI.ElementaryPositivity.SlopeArithmetic.OnSlopeOrZero.compatible` (definitions bundle `OAIQ368Chrom027` of this split); `OAI.ElementaryPositivity.RawShuffle.gridLeadingB` (definitions bundle `OAIQ368Chrom029` of this split).
--
--   **Used by.** The proof of `OAI.ElementaryPositivity.RawShuffle.globalCoproduct_mul` of this split imports it.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/DimensionColumnLeading.lean (declaration OAI.ElementaryPositivity.RawShuffle.unitalSeparationConstant_shuffle_leading_all)

import Mathlib
import Definitions.Def_OAIQ368Chrom029

section

attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.PackConvolution
open HahnSeries SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]
attribute [local instance] Classical.propDecidable

lemma unitalSeparationConstant_shuffle_leading_all (a : I → I → ℕ) (c η : I → ℝ)
    (hc : ∀ i,0 < c i) (θ : ℝ) {d e α β : I → ℕ} (hχ : SlopeEulerSymmetric a c η θ)
    (h : d+e=α+β) (U V : ℤ) (f : S d) (g : S e)
    (hf : quotientAlg a (slope c η) d f∈unitalSourceFiltration a c η hc θ d U)
    (hg : quotientAlg a (slope c η) e g∈unitalSourceFiltration a c η hc θ e V)
    (hα : OnSlopeOrZero c η θ α) (hβ : OnSlopeOrZero c η θ β)
    (hd : OnSlopeOrZero c η θ d)
    {s : Pack (A:=A)} (R : Realization (α+β) s) :
    (unitalSeparationSeries a c η hc (hα.compatible hβ)
      (quotientAlg a (slope c η) (α+β) (castS h (shufflePolynomial a f g)))).coeff 0-
      gridLeadingB a c η hc θ f g (cutRealizationEquiv R (firstCut α β)).val
        (leftRealization R (firstCut α β)) (rightRealization R (firstCut α β))∈
    unitalSourceTensorFiltration a c η hc θ α β (U+V+1) := by
  sorry

end ElementaryPositivity.RawShuffle

end

end OAI
end
