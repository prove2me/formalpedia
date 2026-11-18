-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_RawShuffle_hnPolynomialExpansion_injective
-- name    : OAI.ElementaryPositivity.RawShuffle.hnPolynomialExpansion_injective
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T18:29:18.774862+00:00
-- url     : https://prove2.me/theorems/1f004950-2e53-4c3a-af88-5a5b6088ed7c
-- title:
--   OAI.ElementaryPositivity.RawShuffle.hnPolynomialExpansion_injective: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.RawShuffle.hnPolynomialExpansion_injective` of [lean/OAI/Combinatorics/Chromatic/Shuffle/HNIndependent.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/HNIndependent.lean) at commit 7ef5c0c.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.RawShuffle`, with `open scoped TensorProduct DirectSum` and `open ElementaryPositivity.SlopeArithmetic`, universe `u`, and `variable {I : Type u} [Fintype I] [DecidableEq I]`, `variable (a : I → I → ℕ) (c η : I → ℝ)`):
--
--   ```lean
--   theorem hnPolynomialExpansion_injective (hc : ∀ i,0 < c i)
--       (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d)
--       (hσ : ∀ d,Function.RightInverse (σ d) (destabilizingSpace a (slope c η) d).mkQ) (d : I → ℕ) :
--       Function.Injective (hnPolynomialExpansion a c η σ d)
--   ```
--
--   **In words.** Under the hypotheses `hc` and `hσ`, where each `σ d` is a right inverse of the quotient map of `destabilizingSpace a (slope c η) d`, the statement says that for every `d : I → ℕ` the map `hnPolynomialExpansion a c η σ d` is injective.
--
--   **Definitions.** The statement uses `hnPolynomialExpansion`, `destabilizingSpace`, `slope`, `B` and `S`, written in the definitions bundles `OAIQ368Chrom027`, `OAIQ368Chrom028`, `OAIQ368Chrom033` and `OAIQ368Chrom038` of this split.
--
--   **Used by.** The proof file of this statement imports the published statement `OAI.ElementaryPositivity.RawShuffle.clipped_grid_constant_head` of this split.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Shuffle/HNIndependent.lean (declaration OAI.ElementaryPositivity.RawShuffle.hnPolynomialExpansion_injective)

import Mathlib
import Definitions.Def_OAIQ368Chrom038

section

attribute [-instance] _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAddCommGroup _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instAlgebra _root_.OAI.ElementaryPositivity.QuantumTorus.Torus.instRing _root_.OAI.ElementaryPositivity.RationalFiber.FiberTorus.instRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.RawShuffle
open scoped TensorProduct DirectSum
open ElementaryPositivity.SlopeArithmetic
universe u
variable {I : Type u} [Fintype I] [DecidableEq I]
variable (a : I → I → ℕ) (c η : I → ℝ)

theorem hnPolynomialExpansion_injective (hc : ∀ i,0 < c i)
    (σ : ∀ d,B a (slope c η) d →ₗ[ℚ] S d)
    (hσ : ∀ d,Function.RightInverse (σ d) (destabilizingSpace a (slope c η) d).mkQ) (d : I → ℕ) :
    Function.Injective (hnPolynomialExpansion a c η σ d) := by
  sorry

end ElementaryPositivity.RawShuffle

end

end OAI
end
