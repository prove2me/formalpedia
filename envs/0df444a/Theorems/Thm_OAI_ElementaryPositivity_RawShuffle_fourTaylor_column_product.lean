-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_RawShuffle_fourTaylor_column_product
-- name    : OAI.ElementaryPositivity.RawShuffle.fourTaylor_column_product
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T18:30:47.256545+00:00
-- url     : https://prove2.me/theorems/fdf5b32d-cac5-4b53-902f-83668e92a163
-- title:
--   OAI.ElementaryPositivity.RawShuffle.fourTaylor_column_product: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.RawShuffle.fourTaylor_column_product` of [lean/OAI/Combinatorics/Chromatic/Shuffle/HNDiagonal.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/HNDiagonal.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.RawShuffle`, with `open MvPolynomial HahnSeries`, `open ElementaryPositivity.LaurentAtInfinity SeparationInfinity`, `open scoped TensorProduct`):
--
--   ```lean
--   lemma fourTaylor_column_product (d₁ e₁ d₂ e₂ : I → ℕ)
--       (f : S d₁⊗[ℚ]S d₂) (g : S e₁⊗[ℚ]S e₂) :
--       mapRing (firstColumnAlg d₁ e₁ d₂ e₂).toRingHom (polynomial (relativeTaylor d₁ d₂ f)) *
--         mapRing (secondColumnAlg d₁ e₁ d₂ e₂).toRingHom (polynomial (relativeTaylor e₁ e₂ g))=
--       polynomial (fourRelativeTaylor d₁ e₁ d₂ e₂ (fourInterchange d₁ e₁ d₂ e₂ (f⊗ₜ[ℚ]g)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElementaryPositivity.LaurentAtInfinity.mapRing`, `OAI.ElementaryPositivity.LaurentAtInfinity.polynomial`, `OAI.ElementaryPositivity.RawShuffle.S`, `OAI.ElementaryPositivity.RawShuffle.relativeTaylor` and `OAI.ElementaryPositivity.RawShuffle.symmetricSpace` (definitions bundle `OAIQ368Chrom017` of this split); `OAI.ElementaryPositivity.RawShuffle.cancelFourNonUnital`, `OAI.ElementaryPositivity.RawShuffle.cancelFourRing` and `OAI.ElementaryPositivity.RawShuffle.cancelTensorRing` (definitions bundle `OAIQ368Chrom022` of this split); `OAI.ElementaryPositivity.RawShuffle.fourInterchange` (definitions bundle `OAIQ368Chrom027` of this split); `OAI.ElementaryPositivity.RawShuffle.columnFourAlgebra`, `OAI.ElementaryPositivity.RawShuffle.columnTensorAlgebra`, `OAI.ElementaryPositivity.RawShuffle.firstColumnAlg`, `OAI.ElementaryPositivity.RawShuffle.fourRelativeTaylor`, `OAI.ElementaryPositivity.RawShuffle.secondColumnAlg`, `OAI.ElementaryPositivity.RawShuffle.taylorFourAlgebra` and `OAI.ElementaryPositivity.RawShuffle.taylorTensorAlgebra` (definitions bundle `OAIQ368Chrom033` of this split).
--
--   **Used by.** The proof of `OAI.ElementaryPositivity.RawShuffle.clipped_grid_constant_head` of this split imports it.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/HNDiagonal.lean (declaration OAI.ElementaryPositivity.RawShuffle.fourTaylor_column_product)

import Mathlib
import Definitions.Def_OAIQ368Chrom027
import Definitions.Def_OAIQ368Chrom033

section

attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ElementaryPositivity.RawShuffle
open MvPolynomial HahnSeries
open ElementaryPositivity.LaurentAtInfinity SeparationInfinity
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] cancelTensorRing cancelTensorAlg cancelFourRing cancelFourAlg
attribute [local instance] cancelTensorDistrib cancelTensorSelf cancelTensorNonUnital cancelFourNonUnital cancelSeriesRing
attribute [local instance] cellSepTensorSemiring cellSepTensorNonAssoc cellSepFourSemiring cellSepFourNonAssoc cellSepFourModule

lemma fourTaylor_column_product (d₁ e₁ d₂ e₂ : I → ℕ)
    (f : S d₁⊗[ℚ]S d₂) (g : S e₁⊗[ℚ]S e₂) :
    mapRing (firstColumnAlg d₁ e₁ d₂ e₂).toRingHom (polynomial (relativeTaylor d₁ d₂ f)) *
      mapRing (secondColumnAlg d₁ e₁ d₂ e₂).toRingHom (polynomial (relativeTaylor e₁ e₂ g))=
    polynomial (fourRelativeTaylor d₁ e₁ d₂ e₂ (fourInterchange d₁ e₁ d₂ e₂ (f⊗ₜ[ℚ]g))) := by
  sorry

end ElementaryPositivity.RawShuffle

end OAI
end
