-- Prove2me | Theorems.Thm_MasulloRH_height_two_outer_strip_density_bound
-- name    : MasulloRH.height_two_outer_strip_density_bound
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T12:35:07.753777+00:00
-- url     : https://prove2.me/theorems/edf6d761-2508-40dc-94cf-3095508b9d7b
-- title:
--   Uniform energy density at most two to the minus one hundred on the two outer height-two strips
-- statement:
--   For the exact height-two witness, its weighted squared residual is at most $2^{-100}$ at every point of $[-4,-27/8]\cup[31/8,4]$. This holds for the infinite theta function. These strips contain the first 80 and the final 16 cells of the uniform mesh of step $1/128$.
-- source:
--   Finite-height certificate for https://prove2.me/theorems/cc487734-5ed4-5457-b10a-df505d0aef9e with the rational witness https://prove2.me/definitions/d1967a7a-bf7f-42bd-8ad5-820a7680a39d .

import Definitions.Def_MasulloRH_GaussianThetaApproximation
import Definitions.Def_MasulloRH_HeightTwoWitness

open MasulloRH MasulloRH.GaussianApproximation Set

theorem MasulloRH.height_two_outer_strip_density_bound (x : ℝ) (hx : x ∈ Icc (-4 : ℝ) 4) (hout : x ≤ -27/8 ∨ 31/8 ≤ x) :
    Real.exp (2*(3/4)*x + 2*(11/48)*|x|) *
      ‖residual 2 HeightTwoWitness.coeffs HeightTwoWitness.shifts x‖^2 ≤ 1/(2:ℝ)^100 := by sorry
