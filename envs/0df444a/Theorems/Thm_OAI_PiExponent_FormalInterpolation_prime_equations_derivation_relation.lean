-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_prime_equations_derivation_relation
-- name    : OAI.PiExponent.FormalInterpolation.prime_equations_derivation_relation
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-24T04:33:11.251101+00:00
-- url     : https://prove2.me/theorems/6c4496d6-3271-4395-91fe-13811dd9d1fe
-- title:
--   Derivations of generic coordinates give relations among prime normal columns
-- statement:
--   This isolates the polynomial chain rule, with no exclusion, nonzero-ideal, or Y-invertibility assumption. Evaluate the function-valued identity at an arbitrary equation F∈P. Its image in the fraction field is zero, hence its derivative is zero. The polynomial chain rule identifies that derivative with the displayed sum of mapped partial derivatives multiplied by D(X_i). An independent proof proceeds by polynomial induction using the Leibniz rule, or by comparing pulled-back derivations on generators using the inspected `MvPolynomial.derivation_ext`. Complex-linearity kills constants. The statement also holds for P=⊥ and m=0. The reduction itself performs the subsequent change from coordinate coefficients to logarithmic-frame coefficients.

import Definitions.Def_OAI_PiExponent_LogarithmicNormalBases
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.prime_equations_derivation_relation
    {m : Nat}
    (P : Ideal (MvPolynomial (Fin (m + 1)) Complex)) [P.IsPrime]
    (D : Derivation Complex (logarithmicPrimeField P) (logarithmicPrimeField P)) :
    (∑ i : Fin (m + 1),
      D (algebraMap (MvPolynomial (Fin (m + 1)) Complex)
        (logarithmicPrimeField P) (MvPolynomial.X i)) •
          coordinateNormalColumnAtPrime P i) = 0 := by
  sorry
