-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_RawShuffle_clearedSeparationB_cell
-- name    : OAI.ElementaryPositivity.RawShuffle.clearedSeparationB_cell
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T18:34:20.142652+00:00
-- url     : https://prove2.me/theorems/9704635a-d8e6-4cce-b8e9-5b4a46cfae7a
-- title:
--   OAI.ElementaryPositivity.RawShuffle.clearedSeparationB_cell: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.RawShuffle.clearedSeparationB_cell` of [lean/OAI/Combinatorics/Chromatic/Shuffle/TwoTargetFiltration.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/TwoTargetFiltration.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.RawShuffle`, with `open scoped TensorProduct`, `open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.SlopeArithmetic`, `open HahnSeries SeparationInfinity`):
--
--   ```lean
--   lemma clearedSeparationB_cell (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
--       (d₁ e₁ d₂ e₂ : I → ℕ)
--       (hd : d₁=0 ∨ d₂=0 ∨ slope c η d₁=slope c η d₂)
--       (he : e₁=0 ∨ e₂=0 ∨ slope c η e₁=slope c η e₂)
--       (h₁ : d₁=0 ∨ e₁=0 ∨ slope c η d₁=slope c η e₁)
--       (h₂ : d₂=0 ∨ e₂=0 ∨ slope c η d₂=slope c η e₂)
--       (f : S (d₁+d₂)) (g : S (e₁+e₂)) :
--       clearedSeparationB a (slope c η) (d₁+e₁) (d₂+e₂)
--         (quotientTensor a (slope c η) (d₁+e₁) (d₂+e₂)
--           (cellTransfer a d₁ e₁ d₂ e₂ (fourGridPolynomial a f g d₁ e₁ d₂ e₂)))=
--       ((-1 : ℚ)^eulerForm a d₂ e₁) •
--         mapLinear (twoTargetTransferB a c η hc d₁ e₁ d₂ e₂ h₁ h₂)
--           (fourInputSeriesB a c η hc d₁ e₁ d₂ e₂ hd he
--             (quotientAlg a (slope c η) (d₁+d₂) f) (quotientAlg a (slope c η) (e₁+e₂) g))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElementaryPositivity.LaurentAtInfinity.mapLinear`, `OAI.ElementaryPositivity.RawShuffle.B`, `OAI.ElementaryPositivity.RawShuffle.CellVars`, `OAI.ElementaryPositivity.RawShuffle.S`, `OAI.ElementaryPositivity.RawShuffle.cellTransfer`, `OAI.ElementaryPositivity.RawShuffle.destabilizingSpace`, `OAI.ElementaryPositivity.RawShuffle.eulerForm`, `OAI.ElementaryPositivity.RawShuffle.quotientAlg`, `OAI.ElementaryPositivity.RawShuffle.quotientAlgebra`, `OAI.ElementaryPositivity.RawShuffle.quotientCommRing`, `OAI.ElementaryPositivity.RawShuffle.quotientTensor`, `OAI.ElementaryPositivity.RawShuffle.symmetricSpace` and `OAI.ElementaryPositivity.SlopeArithmetic.slope` (definitions bundle `OAIQ368Chrom017` of this split); `OAI.ElementaryPositivity.RawShuffle.fourGridPolynomial` (definitions bundle `OAIQ368Chrom022` of this split); `OAI.ElementaryPositivity.RawShuffle.twoTargetTransferB` (definitions bundle `OAIQ368Chrom027` of this split); `OAI.ElementaryPositivity.RawShuffle.clearedSeparationB` (definitions bundle `OAIQ368Chrom028` of this split); `OAI.ElementaryPositivity.RawShuffle.fourInputSeriesB` (definitions bundle `OAIQ368Chrom037` of this split).
--
--   **Used by.** The proof of `OAI.ElementaryPositivity.RawShuffle.unitalSeparationConstant_shuffle_leading_all` of this split imports it.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/TwoTargetFiltration.lean (declaration OAI.ElementaryPositivity.RawShuffle.clearedSeparationB_cell)

import Mathlib
import Definitions.Def_OAIQ368Chrom037

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
open ElementaryPositivity.LaurentAtInfinity ElementaryPositivity.SlopeArithmetic
open HahnSeries SeparationInfinity
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] cancelTensorRing cancelTensorAlg cancelFourRing cancelFourAlg
attribute [local instance] cancelTensorSelf cancelTensorNonUnital cancelFourNonUnital cancelSeriesRing
attribute [local instance] cellSepTensorSemiring cellSepTensorNonAssoc cellSepFourSemiring cellSepFourNonAssoc cellSepFourModule
attribute [local instance] braidFourTensor braidFourTensorAlg braidFourRing braidFourAlg
attribute [local instance] braidFourTensorN braidFourTensorM braidFourN braidFourM

lemma clearedSeparationB_cell (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (d₁ e₁ d₂ e₂ : I → ℕ)
    (hd : d₁=0 ∨ d₂=0 ∨ slope c η d₁=slope c η d₂)
    (he : e₁=0 ∨ e₂=0 ∨ slope c η e₁=slope c η e₂)
    (h₁ : d₁=0 ∨ e₁=0 ∨ slope c η d₁=slope c η e₁)
    (h₂ : d₂=0 ∨ e₂=0 ∨ slope c η d₂=slope c η e₂)
    (f : S (d₁+d₂)) (g : S (e₁+e₂)) :
    clearedSeparationB a (slope c η) (d₁+e₁) (d₂+e₂)
      (quotientTensor a (slope c η) (d₁+e₁) (d₂+e₂)
        (cellTransfer a d₁ e₁ d₂ e₂ (fourGridPolynomial a f g d₁ e₁ d₂ e₂)))=
    ((-1 : ℚ)^eulerForm a d₂ e₁) •
      mapLinear (twoTargetTransferB a c η hc d₁ e₁ d₂ e₂ h₁ h₂)
        (fourInputSeriesB a c η hc d₁ e₁ d₂ e₂ hd he
          (quotientAlg a (slope c η) (d₁+d₂) f) (quotientAlg a (slope c η) (e₁+e₂) g)) := by
  sorry

end ElementaryPositivity.RawShuffle

end

end OAI
end
