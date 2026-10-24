-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_truncatedPolynomialJet_monomialCoeff_eq_entry
-- name    : OAI.PiExponent.DeterminantContradiction.truncatedPolynomialJet_monomialCoeff_eq_entry
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T17:01:52.53574+00:00
-- url     : https://prove2.me/theorems/254e46eb-9c60-4b80-a50d-454e999dae81
-- title:
--   A truncated jet monomial coefficient equals its iterated matrix entry
-- statement:
--   For arbitrary centers and truncation orders, the coefficient of a monomial after truncated-jet substitution equals the corresponding iterated coefficient entry. The statement includes dimension zero, zero exponents, and zero truncation orders.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.truncatedPolynomialJet_monomialCoeff_eq_entry
    (m : Nat) (r : Fin m → Complex) (T : Fin m → Nat)
    (j s h : Nat) (b a : Fin m → Nat) :
    (truncatedPolynomialJet (fun i => (j : Complex) * r i) T
      (MvPolynomial.monomial (InterpolationMatrix.exponentVector (Fin.cases h a)) 1)).coeff
      (InterpolationMatrix.exponentVector (Fin.cases s b)) =
      InterpolationMatrix.entry r
        (fun i => InterpolationMatrix.truncatedLog (T i)) j s b h a := by sorry
