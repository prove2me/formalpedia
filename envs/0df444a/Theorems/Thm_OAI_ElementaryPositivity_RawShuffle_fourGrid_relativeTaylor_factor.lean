-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_RawShuffle_fourGrid_relativeTaylor_factor
-- name    : OAI.ElementaryPositivity.RawShuffle.fourGrid_relativeTaylor_factor
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T18:29:18.642587+00:00
-- url     : https://prove2.me/theorems/37957ec8-5bd6-41e2-bfa7-1cc795278bd6
-- title:
--   OAI.ElementaryPositivity.RawShuffle.fourGrid_relativeTaylor_factor: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.RawShuffle.fourGrid_relativeTaylor_factor` of [lean/OAI/Combinatorics/Chromatic/Shuffle/CellSeparation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/CellSeparation.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.RawShuffle`, with `open MvPolynomial HahnSeries`, `open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.RectangularKernel`, `open SeparationInfinity`, `open scoped TensorProduct`):
--
--   ```lean
--   lemma fourGrid_relativeTaylor_factor (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
--       (f : S (d₁+d₂)) (g : S (e₁+e₂)) :
--       fourRelativeTaylor d₁ e₁ d₂ e₂
--         (separateFour d₁ e₁ d₂ e₂ (fourGridPolynomial a f g d₁ e₁ d₂ e₂))=
--       Polynomial.map (firstColumnAlg d₁ e₁ d₂ e₂).toRingHom
--         (relativeTaylor d₁ d₂ (restrictTensor (firstCut d₁ d₂) f)) *
--       Polynomial.map (secondColumnAlg d₁ e₁ d₂ e₂).toRingHom
--         (relativeTaylor e₁ e₂ (restrictTensor (firstCut e₁ e₂) g)) *
--       fourRelativeTaylor d₁ e₁ d₂ e₂ (fourCrossTensor a d₁ e₁ d₂ e₂)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElementaryPositivity.RawShuffle.CellVars`, `OAI.ElementaryPositivity.RawShuffle.S`, `OAI.ElementaryPositivity.RawShuffle.firstCut`, `OAI.ElementaryPositivity.RawShuffle.relativeTaylor`, `OAI.ElementaryPositivity.RawShuffle.restrictTensor`, `OAI.ElementaryPositivity.RawShuffle.separateFour` and `OAI.ElementaryPositivity.RawShuffle.symmetricSpace` (definitions bundle `OAIQ368Chrom017` of this split); `OAI.ElementaryPositivity.RawShuffle.fourGridPolynomial` (definitions bundle `OAIQ368Chrom022` of this split); `OAI.ElementaryPositivity.RawShuffle.cellSepFourSemiring` and `OAI.ElementaryPositivity.RawShuffle.cellSepTensorSemiring` (definitions bundle `OAIQ368Chrom023` of this split); `OAI.ElementaryPositivity.RawShuffle.fourCrossTensor` (definitions bundle `OAIQ368Chrom027` of this split); `OAI.ElementaryPositivity.RawShuffle.columnFourAlgebra`, `OAI.ElementaryPositivity.RawShuffle.columnTensorAlgebra`, `OAI.ElementaryPositivity.RawShuffle.firstColumnAlg`, `OAI.ElementaryPositivity.RawShuffle.fourRelativeTaylor`, `OAI.ElementaryPositivity.RawShuffle.secondColumnAlg`, `OAI.ElementaryPositivity.RawShuffle.taylorFourAlgebra` and `OAI.ElementaryPositivity.RawShuffle.taylorTensorAlgebra` (definitions bundle `OAIQ368Chrom033` of this split).
--
--   **Used by.** The proof of `OAI.ElementaryPositivity.RawShuffle.fourGrid_taylor_factor` of this split imports it.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/CellSeparation.lean (declaration OAI.ElementaryPositivity.RawShuffle.fourGrid_relativeTaylor_factor)

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
lemma fourGrid_relativeTaylor_factor (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (f : S (d₁+d₂)) (g : S (e₁+e₂)) :
    fourRelativeTaylor d₁ e₁ d₂ e₂
      (separateFour d₁ e₁ d₂ e₂ (fourGridPolynomial a f g d₁ e₁ d₂ e₂))=
    Polynomial.map (firstColumnAlg d₁ e₁ d₂ e₂).toRingHom
      (relativeTaylor d₁ d₂ (restrictTensor (firstCut d₁ d₂) f)) *
    Polynomial.map (secondColumnAlg d₁ e₁ d₂ e₂).toRingHom
      (relativeTaylor e₁ e₂ (restrictTensor (firstCut e₁ e₂) g)) *
    fourRelativeTaylor d₁ e₁ d₂ e₂ (fourCrossTensor a d₁ e₁ d₂ e₂) := by
  sorry

end ElementaryPositivity.RawShuffle

end OAI
end
