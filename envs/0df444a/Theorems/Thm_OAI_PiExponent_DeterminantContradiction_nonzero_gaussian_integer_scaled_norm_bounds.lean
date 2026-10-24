-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_nonzero_gaussian_integer_scaled_norm_bounds
-- name    : OAI.PiExponent.DeterminantContradiction.nonzero_gaussian_integer_scaled_norm_bounds
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T08:57:50.150047+00:00
-- url     : https://prove2.me/theorems/6330e0e8-75cd-425e-810b-5e933b84c9de
-- title:
--   Norm bounds from a nonzero Gaussian integer
-- statement:
--   If a nonzero complex number becomes a Gaussian integer after multiplication by a positive integer D, then its scaled norm is at least one and its norm is at least 1/D. The proof uses that the integer coordinates are not both zero, then applies norm multiplicativity and logarithm monotonicity.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.DeterminantContradiction.nonzero_gaussian_integer_scaled_norm_bounds
    {z : Complex} (hz : z ≠ 0) (D : Nat) (hD : 0 < D)
    (a b : Int)
    (hscale : (D : Complex) * z = (a : Complex) + Complex.I * (b : Complex)) :
    1 ≤ (D : Real) * ‖z‖ ∧
      -(Real.log (D : Real)) ≤ Real.log ‖z‖ := by
  sorry
