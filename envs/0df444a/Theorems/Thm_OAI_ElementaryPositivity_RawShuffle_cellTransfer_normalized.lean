-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_RawShuffle_cellTransfer_normalized
-- name    : OAI.ElementaryPositivity.RawShuffle.cellTransfer_normalized
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T18:33:52.702895+00:00
-- url     : https://prove2.me/theorems/4f50ac53-9ccd-46ba-a4bc-0bbc9a66bae4
-- title:
--   OAI.ElementaryPositivity.RawShuffle.cellTransfer_normalized: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.RawShuffle.cellTransfer_normalized` of [lean/OAI/Combinatorics/Chromatic/Shuffle/CellTransferSeparation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/CellTransferSeparation.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.RawShuffle`, with `open MvPolynomial HahnSeries`, `open ElementaryPositivity.LaurentAtInfinity SeparationInfinity`, `open scoped TensorProduct`):
--
--   ```lean
--   lemma cellTransfer_normalized (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
--       (f : S (d₁+d₂)) (g : S (e₁+e₂)) :
--       ((inverseKernelUnit a (d₁+e₁) (d₂+e₂))*
--         (inverseKernelUnit (fun _ _ : I=>0) (d₁+e₁) (d₂+e₂))⁻¹).val *
--         polynomial (relativeTaylor (d₁+e₁) (d₂+e₂)
--           (cellTransfer a d₁ e₁ d₂ e₂ (fourGridPolynomial a f g d₁ e₁ d₂ e₂)))=
--       ((-1 : ℚ)^eulerForm a d₂ e₁) •
--         mapLinear (twoTargetTransfer a d₁ e₁ d₂ e₂) (fourInputSeries a d₁ e₁ d₂ e₂ f g)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElementaryPositivity.LaurentAtInfinity.mapLinear`, `OAI.ElementaryPositivity.LaurentAtInfinity.polynomial`, `OAI.ElementaryPositivity.RawShuffle.CellVars`, `OAI.ElementaryPositivity.RawShuffle.S`, `OAI.ElementaryPositivity.RawShuffle.cellTransfer`, `OAI.ElementaryPositivity.RawShuffle.eulerForm`, `OAI.ElementaryPositivity.RawShuffle.relativeTaylor`, `OAI.ElementaryPositivity.RawShuffle.symmetricSpace` and `OAI.ElementaryPositivity.RawShuffle.twoTargetTransfer` (definitions bundle `OAIQ368Chrom017` of this split); `OAI.ElementaryPositivity.RawShuffle.cancelTensorNonUnital`, `OAI.ElementaryPositivity.RawShuffle.cancelTensorRing`, `OAI.ElementaryPositivity.RawShuffle.fourGridPolynomial` and `OAI.ElementaryPositivity.RawShuffle.SeparationInfinity.inverseKernelUnit` (definitions bundle `OAIQ368Chrom022` of this split); `OAI.ElementaryPositivity.RawShuffle.fourInputSeries` (definitions bundle `OAIQ368Chrom036` of this split).
--
--   **Used by.** The proofs of `OAI.ElementaryPositivity.RawShuffle.clearedSeparationB_cell` and `OAI.ElementaryPositivity.RawShuffle.clipped_grid_constant_head` of this split import it.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/CellTransferSeparation.lean (declaration OAI.ElementaryPositivity.RawShuffle.cellTransfer_normalized)

import Mathlib
import Definitions.Def_OAIQ368Chrom036

section

attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instMul _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instMul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial HahnSeries
open ElementaryPositivity.LaurentAtInfinity SeparationInfinity
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] cancelTensorRing cancelTensorAlg cancelFourRing cancelFourAlg
attribute [local instance] cancelTensorSelf cancelTensorNonUnital cancelFourNonUnital cancelSeriesRing
attribute [local instance] cellSepTensorSemiring cellSepTensorNonAssoc cellSepFourSemiring cellSepFourNonAssoc cellSepFourModule

lemma cellTransfer_normalized (a : I → I → ℕ) (d₁ e₁ d₂ e₂ : I → ℕ)
    (f : S (d₁+d₂)) (g : S (e₁+e₂)) :
    ((inverseKernelUnit a (d₁+e₁) (d₂+e₂))*
      (inverseKernelUnit (fun _ _ : I=>0) (d₁+e₁) (d₂+e₂))⁻¹).val *
      polynomial (relativeTaylor (d₁+e₁) (d₂+e₂)
        (cellTransfer a d₁ e₁ d₂ e₂ (fourGridPolynomial a f g d₁ e₁ d₂ e₂)))=
    ((-1 : ℚ)^eulerForm a d₂ e₁) •
      mapLinear (twoTargetTransfer a d₁ e₁ d₂ e₂) (fourInputSeries a d₁ e₁ d₂ e₂ f g) := by
  sorry

end ElementaryPositivity.RawShuffle

end

end OAI
end
