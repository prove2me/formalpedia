-- Prove2me | Theorems.Thm_MasulloRH_height_two_energy_bound_from_central_interval
-- name    : MasulloRH.height_two_energy_bound_from_central_interval
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T13:29:15.3968+00:00
-- url     : https://prove2.me/theorems/5e8c704f-384f-5f40-93d7-e6572c31fbfe
-- title:
--   Whole-line height-two energy from its integral on the central interval
-- statement:
--   For the published eleven rational height-two coefficients and shifts, let $R$ be the canonical residual and $F(x)=\exp(3x/2+11|x|/24)|R(x)|^2$. Then $F$ is integrable and its whole-line energy is at most its integral on $[-23/8,7/2]$ plus $13/800000000+10^{-10}$. The entire omitted contribution is therefore at most $0.00000001635$.
-- source:
--   The Masullo height-two theta-energy calculation https://prove2.me/theorems/cc487734-5ed4-5457-b10a-df505d0aef9e and its curvature-row theorem https://prove2.me/theorems/680e75e0-46e9-4f05-b70c-7f7de8530930.

import Definitions.Def_MasulloRH_HeightTwoCurvature
import Definitions.Def_MasulloRH_GaussianThetaApproximation

open MasulloRH MasulloRH.GaussianApproximation MeasureTheory Set

theorem MasulloRH.height_two_energy_bound_from_central_interval :
    let R := residual 2 HeightTwoWitness.coeffs HeightTwoWitness.shifts
    let F := fun x : ℝ => Real.exp (2*(3/4)*x+2*(11/48)*|x|)*‖R x‖^2
    Integrable F ∧ energy (3/4) (11/48) R ≤ (∫ x : ℝ in Icc (-23/8) (7/2), F x) +
      13/800000000 + 1/10000000000 := by sorry
