-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_RawShuffle_clipped_grid_constant_head
-- name    : OAI.ElementaryPositivity.RawShuffle.clipped_grid_constant_head
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T18:32:07.269317+00:00
-- url     : https://prove2.me/theorems/64df125b-97d9-472e-a989-97caa83cd42b
-- title:
--   OAI.ElementaryPositivity.RawShuffle.clipped_grid_constant_head: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.RawShuffle.clipped_grid_constant_head` of [lean/OAI/Combinatorics/Chromatic/Shuffle/CutoffGrid.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/CutoffGrid.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.RawShuffle`, with `open MvPolynomial HahnSeries`, `open ElementaryPositivity.LaurentAtInfinity SeparationInfinity`, `open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.PackConvolution`, `open scoped TensorProduct`):
--
--   ```lean
--   lemma clipped_grid_constant_head (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
--       (κ : ℝ) {d e : I → ℕ} (f : S d) (g : S e) {s : Pack (A:=A)} (p : PackConvolution.Cut s)
--       (R : Realization d (left p)) (T : Realization e (right p)) (hd : d≠0)
--       (hk : κ < slope c η d) (ht : slope c η e ≤ κ) :
--       clearedConstantB a (clippedSlope c η κ) d e
--         (quotientTensor a (clippedSlope c η κ) d e (gridTensor a f g p R T))=
--       quotientTensor a (clippedSlope c η κ) d e (f⊗ₜ[ℚ]g)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ElementaryPositivity.PackConvolution.Cut`, `OAI.ElementaryPositivity.PackConvolution.Pack`, `OAI.ElementaryPositivity.PackConvolution.left`, `OAI.ElementaryPositivity.PackConvolution.right`, `OAI.ElementaryPositivity.RawShuffle.B`, `OAI.ElementaryPositivity.RawShuffle.Realization`, `OAI.ElementaryPositivity.RawShuffle.S`, `OAI.ElementaryPositivity.RawShuffle.destabilizingSpace`, `OAI.ElementaryPositivity.RawShuffle.quotientAlgebra`, `OAI.ElementaryPositivity.RawShuffle.quotientCommRing`, `OAI.ElementaryPositivity.RawShuffle.quotientTensor`, `OAI.ElementaryPositivity.RawShuffle.symmetricSpace` and `OAI.ElementaryPositivity.SlopeArithmetic.slope` (definitions bundle `OAIQ368Chrom017` of this split); `OAI.ElementaryPositivity.RawShuffle.gridTensor` (definitions bundle `OAIQ368Chrom022` of this split); `OAI.ElementaryPositivity.RawShuffle.clearedConstantB` (definitions bundle `OAIQ368Chrom028` of this split); `OAI.ElementaryPositivity.SlopeArithmetic.clippedSlope` (definitions bundle `OAIQ368Chrom038` of this split).
--
--   **Used by.** The proof of `OAI.ElementaryPositivity.RawShuffle.hnPolynomialExpansion_injective` of this split imports it.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/CutoffGrid.lean (declaration OAI.ElementaryPositivity.RawShuffle.clipped_grid_constant_head)

import Mathlib
import Definitions.Def_OAIQ368Chrom028
import Definitions.Def_OAIQ368Chrom038

section

attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing _root_.OAI.ElementaryPositivity.WeightedTorusSeries.sliceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open MvPolynomial HahnSeries
open ElementaryPositivity.LaurentAtInfinity SeparationInfinity
open ElementaryPositivity.SlopeArithmetic ElementaryPositivity.PackConvolution
open scoped TensorProduct
variable {I : Type*} [Fintype I] [DecidableEq I]
attribute [local instance] clearBTensorB clearBTensorBA

variable {A : I → Type*} [∀ i,Fintype (A i)] [∀ i,DecidableEq (A i)]

omit [∀ i, Fintype (A i)] in
lemma clipped_grid_constant_head (a : I → I → ℕ) (c η : I → ℝ) (hc : ∀ i,0 < c i)
    (κ : ℝ) {d e : I → ℕ} (f : S d) (g : S e) {s : Pack (A:=A)} (p : PackConvolution.Cut s)
    (R : Realization d (left p)) (T : Realization e (right p)) (hd : d≠0)
    (hk : κ < slope c η d) (ht : slope c η e ≤ κ) :
    clearedConstantB a (clippedSlope c η κ) d e
      (quotientTensor a (clippedSlope c η κ) d e (gridTensor a f g p R T))=
    quotientTensor a (clippedSlope c η κ) d e (f⊗ₜ[ℚ]g) := by
  sorry

end ElementaryPositivity.RawShuffle

end

end OAI
end
