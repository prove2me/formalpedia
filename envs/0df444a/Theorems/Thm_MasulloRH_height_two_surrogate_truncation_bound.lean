-- Prove2me | Theorems.Thm_MasulloRH_height_two_surrogate_truncation_bound
-- name    : MasulloRH.height_two_surrogate_truncation_bound
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T12:35:08.091608+00:00
-- url     : https://prove2.me/theorems/488a7130-9829-4819-b875-04e608bc2688
-- title:
--   A six-term truncation bound for the signed eleven-translate height-two residual
-- statement:
--   Use the eleven rational coefficients and shifts of the height-two witness. For grid index $j$ fix the direct or reflected representation of each translate at the left endpoint. Truncate the half-theta expansion after six terms. At every real $x$, the complex norm of the difference between the true signed residual and this real surrogate is bounded by the sum of the eleven absolute-coefficient-weighted geometric tails. The cell index fixes the representation even when the evaluation point lies outside the cell.
-- source:
--   Finite-height certificate for https://prove2.me/theorems/cc487734-5ed4-5457-b10a-df505d0aef9e with the rational witness https://prove2.me/definitions/d1967a7a-bf7f-42bd-8ad5-820a7680a39d .

import Definitions.Def_MasulloRH_GaussianThetaApproximation
import Definitions.Def_MasulloRH_HeightTwoCurvature

open MasulloRH MasulloRH.GaussianApproximation MasulloRH.HeightTwoCurvature

theorem MasulloRH.height_two_surrogate_truncation_bound (j : ℕ) (x : ℝ) :
    ‖residual 2 HeightTwoWitness.coeffs HeightTwoWitness.shifts x - (surrogate j x : ℂ)‖ ≤
      tail j x := by sorry
