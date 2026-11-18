-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_RawShuffle_fourGrid_normalized_algebra
-- name    : OAI.ElementaryPositivity.RawShuffle.fourGrid_normalized_algebra
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T18:34:01.007418+00:00
-- url     : https://prove2.me/theorems/1e0ad679-79e9-4102-88c9-f27e3c917ba1
-- title:
--   OAI.ElementaryPositivity.RawShuffle.fourGrid_normalized_algebra: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.RawShuffle.fourGrid_normalized_algebra` of [lean/OAI/Combinatorics/Chromatic/Shuffle/CellSeparation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/CellSeparation.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.RawShuffle`, with `open MvPolynomial HahnSeries`, `open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.RectangularKernel`, `open SeparationInfinity`, `open scoped TensorProduct`):
--
--   ```lean
--   lemma fourGrid_normalized_algebra (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
--       (f : S (d₁+d₂)) (g : S (e₁+e₂))
--       (K L r : LaurentSeries ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)))
--       (h : K*L*polynomial (fourRelativeTaylor d₁ e₁ d₂ e₂ (fourCrossTensor a d₁ e₁ d₂ e₂))=
--         r*((fourFirstInverseUnit a d₁ e₁ d₂ e₂).val *
--           (fourSecondInverseUnit a d₁ e₁ d₂ e₂).val *
--           (fourCrossingInverseUnit a d₁ e₁ d₂ e₂ *
--             (fourCrossingInverseUnit (fun i j=>a j i) d₁ e₁ d₂ e₂)⁻¹).val)) :
--       K*L*polynomial (fourRelativeTaylor d₁ e₁ d₂ e₂
--         (separateFour d₁ e₁ d₂ e₂ (fourGridPolynomial a f g d₁ e₁ d₂ e₂)))=
--         r*fourInputSeries a d₁ e₁ d₂ e₂ f g
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElementaryPositivity.LaurentAtInfinity.polynomial`, `OAI.ElementaryPositivity.RawShuffle.CellVars`, `OAI.ElementaryPositivity.RawShuffle.S`, `OAI.ElementaryPositivity.RawShuffle.separateFour` and `OAI.ElementaryPositivity.RawShuffle.symmetricSpace` (definitions bundle `OAIQ368Chrom017` of this split); `OAI.ElementaryPositivity.RawShuffle.cancelFourNonUnital`, `OAI.ElementaryPositivity.RawShuffle.cancelFourRing`, `OAI.ElementaryPositivity.RawShuffle.cancelTensorAlg`, `OAI.ElementaryPositivity.RawShuffle.cancelTensorRing` and `OAI.ElementaryPositivity.RawShuffle.fourGridPolynomial` (definitions bundle `OAIQ368Chrom022` of this split); `OAI.ElementaryPositivity.RawShuffle.fourCrossTensor` (definitions bundle `OAIQ368Chrom027` of this split); `OAI.ElementaryPositivity.RawShuffle.fourCrossingInverseUnit`, `OAI.ElementaryPositivity.RawShuffle.fourFirstInverseUnit`, `OAI.ElementaryPositivity.RawShuffle.fourRelativeTaylor`, `OAI.ElementaryPositivity.RawShuffle.fourSecondInverseUnit`, `OAI.ElementaryPositivity.RawShuffle.taylorFourAlgebra` and `OAI.ElementaryPositivity.RawShuffle.taylorTensorAlgebra` (definitions bundle `OAIQ368Chrom033` of this split); `OAI.ElementaryPositivity.RawShuffle.fourInputSeries` (definitions bundle `OAIQ368Chrom036` of this split).
--
--   **Used by.** The proof of `OAI.ElementaryPositivity.RawShuffle.cellTransfer_normalized` of this split imports it.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/CellSeparation.lean (declaration OAI.ElementaryPositivity.RawShuffle.fourGrid_normalized_algebra)

import Mathlib
import Definitions.Def_OAIQ368Chrom036

section

attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ElementaryPositivity.RawShuffle
open MvPolynomial HahnSeries
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.RectangularKernel
open SeparationInfinity
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] cancelTensorRing cancelTensorAlg cancelFourRing cancelFourAlg
attribute [local instance] cancelTensorSelf cancelTensorNonUnital cancelFourNonUnital cancelSeriesRing

attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cellSepTensorSemiring
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cellSepTensorNonAssoc
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cellSepFourSemiring
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cellSepFourNonAssoc
attribute [local instance] OAI.ElementaryPositivity.RawShuffle.cellSepFourModule
lemma fourGrid_normalized_algebra (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (f : S (d₁+d₂)) (g : S (e₁+e₂))
    (K L r : LaurentSeries ((S d₁⊗[ℚ]S e₁)⊗[ℚ](S d₂⊗[ℚ]S e₂)))
    (h : K*L*polynomial (fourRelativeTaylor d₁ e₁ d₂ e₂ (fourCrossTensor a d₁ e₁ d₂ e₂))=
      r*((fourFirstInverseUnit a d₁ e₁ d₂ e₂).val *
        (fourSecondInverseUnit a d₁ e₁ d₂ e₂).val *
        (fourCrossingInverseUnit a d₁ e₁ d₂ e₂ *
          (fourCrossingInverseUnit (fun i j=>a j i) d₁ e₁ d₂ e₂)⁻¹).val)) :
    K*L*polynomial (fourRelativeTaylor d₁ e₁ d₂ e₂
      (separateFour d₁ e₁ d₂ e₂ (fourGridPolynomial a f g d₁ e₁ d₂ e₂)))=
      r*fourInputSeries a d₁ e₁ d₂ e₂ f g := by
  sorry

end ElementaryPositivity.RawShuffle

end OAI
end
