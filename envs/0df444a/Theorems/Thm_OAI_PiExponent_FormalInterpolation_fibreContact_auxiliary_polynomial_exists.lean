-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_fibreContact_auxiliary_polynomial_exists
-- name    : OAI.PiExponent.FormalInterpolation.fibreContact_auxiliary_polynomial_exists
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-21T09:44:03.743648+00:00
-- url     : https://prove2.me/theorems/c4ea55df-1318-41bb-a49e-5f3084041ffd
-- title:
--   Auxiliary polynomials from strict weighted jet volume
-- statement:
--   Strict weighted volume yields nonzero polynomials of degree at most N with Taylor coefficients vanishing strictly below aN, for every sufficiently large integer N. Prove this by weighted lattice counting and a nonzero kernel of the coefficient evaluation map. No center distinctness is required.
-- source:
--   openai/math Approximation FibreNormalRigidity: nonconstant fibre coordinates imply quantitative contact bound.

import Definitions.Def_OAI_PiExponent_FibreContactAuxiliaryData

open scoped BigOperators
open OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.fibreContact_auxiliary_polynomial_exists
    (n K : Nat) (W V : Fin n → Rat)
    (hW : ∀ i, 0 < (W i : Real)) (hV : ∀ i, 0 < (V i : Real))
    (a : Real) (ha : 0 < a)
    (hvolume : (K : Real) * a ^ n *
      (∏ i : Fin n, (W i : Real)) / (∏ i : Fin n, (V i : Real)) < 1)
    (c : Fin K → Fin n → Complex) :
    ∃ N0 : Nat, ∀ N : Nat, N0 ≤ N →
      ∃ F : MvPolynomial (Fin n) Complex,
        F ≠ 0 ∧ fibreContactSupportBound W N F ∧
          fibreContactJetVanishing c V (a * (N : Real)) F := by sorry
