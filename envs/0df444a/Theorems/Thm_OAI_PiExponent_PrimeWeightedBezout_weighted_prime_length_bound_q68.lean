-- Prove2me | Theorems.Thm_OAI_PiExponent_PrimeWeightedBezout_weighted_prime_length_bound_q68
-- name    : OAI.PiExponent.PrimeWeightedBezout.weighted_prime_length_bound_q68
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T08:18:57.750981+00:00
-- url     : https://prove2.me/theorems/c7a09622-72ef-44d9-8274-334aa99057d1
-- title:
--   OAI.PiExponent.PrimeWeightedBezout.weighted_prime_length_bound_q68: intermediate lemma from OpenAI, The irrationality exponent of pi is 2 (result family 017)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PiExponent.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The irrationality exponent of pi is 2 (result family 017)*, OpenAI Math Release, September 24, 2026, result family 17, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PiExponent.PrimeWeightedBezout.weighted_prime_length_bound` of [lean/OAI/NumberTheory/PiExponent/LocalAlgebra/PrimeWeightedBezout.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/LocalAlgebra/PrimeWeightedBezout.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PiExponent.PrimeWeightedBezout`, with `open scoped BigOperators`, `open CoordinateFiniteSlice CoordinateSliceComparison NormalBasisRigidity WeightedSliceDegree`):
--
--   ```lean
--   theorem weighted_prime_length_bound_q68 {n : ℕ}
--       (Q : Ideal (MvPolynomial (Fin n) ℂ)) [Q.IsPrime]
--       (A : Finset (Fin n))
--       (hA : IsNormalBasis (K := Q.ResidueField)
--         (fun i => (polynomialTangent (primeResidueMap Q) Q).mkQ
--           (Pi.basisFun Q.ResidueField _ i)) A)
--       {J : Type*} (f : J → MvPolynomial (Fin n) ℂ)
--       (hQ : Q ∈ (Ideal.span (Set.range f)).minimalPrimes)
--       (rho : Fin n → ℚ) (hrho : ∀ i, 0 < rho i)
--       (N : ℝ) (hN : 0 ≤ N)
--       (hdegree : ∀ j, ∀ d ∈ (f j).support,
--         (∑ i ∈ d.support, (d i : ℝ) * (rho i : ℝ)) ≤ N) :
--       ∃ L : ℕ, primeLength Q (Ideal.span (Set.range f)) = L ∧
--         (L : ℝ) ≤ N ^ A.card / ∏ i ∈ A, (rho i : ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PiExponent.CoordinateSliceComparison.primeLength` (definitions bundle `OAIQ068A006` of this split); `OAI.PiExponent.polynomialTangent`, `OAI.PiExponent.primeResidueMap` and `OAI.PiExponent.NormalBasisRigidity.IsNormalBasis` (definitions bundle `OAIQ068A007` of this split).
--
--   **Used by.** The proofs of `OAI.PiExponent.PersistentWeightComparison.ordinary_persistent_comparison_q68` and `OAI.PiExponent.TransverseSliceComparison.comparison_of_normal_basis_q68` of this split import it.
-- source:
--   OpenAI, The irrationality exponent of pi is 2 (result family 017), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 17; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/LocalAlgebra/PrimeWeightedBezout.lean (declaration OAI.PiExponent.PrimeWeightedBezout.weighted_prime_length_bound)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ068A006
import Definitions.Def_OAIQ068A007

section

attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.PrimeWeightedBezout

open scoped BigOperators
open CoordinateFiniteSlice CoordinateSliceComparison NormalBasisRigidity WeightedSliceDegree

theorem weighted_prime_length_bound_q68 {n : ℕ}
    (Q : Ideal (MvPolynomial (Fin n) ℂ)) [Q.IsPrime]
    (A : Finset (Fin n))
    (hA : IsNormalBasis (K := Q.ResidueField)
      (fun i => (polynomialTangent (primeResidueMap Q) Q).mkQ
        (Pi.basisFun Q.ResidueField _ i)) A)
    {J : Type*} (f : J → MvPolynomial (Fin n) ℂ)
    (hQ : Q ∈ (Ideal.span (Set.range f)).minimalPrimes)
    (rho : Fin n → ℚ) (hrho : ∀ i, 0 < rho i)
    (N : ℝ) (hN : 0 ≤ N)
    (hdegree : ∀ j, ∀ d ∈ (f j).support,
      (∑ i ∈ d.support, (d i : ℝ) * (rho i : ℝ)) ≤ N) :
    ∃ L : ℕ, primeLength Q (Ideal.span (Set.range f)) = L ∧
      (L : ℝ) ≤ N ^ A.card / ∏ i ∈ A, (rho i : ℝ) := by
  sorry

end PiExponent.PrimeWeightedBezout
end

end OAI
end
