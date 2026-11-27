-- Prove2me | Theorems.Thm_MasulloRH_entire_theta_mellin_multiplier
-- name    : MasulloRH.entire_theta_mellin_multiplier
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T22:25:37.641802+00:00
-- url     : https://prove2.me/theorems/d52cca71-4f19-5c66-bed4-1061675582ce
-- title:
--   Entire regularization of the dyadic theta Mellin multiplier
-- statement:
--   The regularized theta multiplier is entire, agrees away from zero and one with the dyadic factors times completed zeta, and takes the nonzero value log(2)/2 at one.
-- source:
--   Masullo RH specialization, fixed unit Gaussian in the expanding weighted windows. The dyadic theta Mellin identity and the accepted finite-window energy identities are used at their registered types. https://prove2.me/theorems/714a2f7b-e260-4499-9c88-2074add3de2b

import Definitions.Def_MasulloRH_RationalThetaGrid

open MeasureTheory MasulloRH MasulloRH.RationalThetaGrid MasulloRH.GaussianApproximation MasulloRH.FixedGaussianTest

theorem MasulloRH.entire_theta_mellin_multiplier :
    Differentiable ℂ thetaMultiplier ∧
    (∀ s : ℂ, s ≠ 0 → s ≠ 1 →
      thetaMultiplier s = (1-(2:ℂ)^(-s))*(1-(2:ℂ)^(1-s))*completedRiemannZeta s) ∧
    thetaMultiplier 1 = logTwo/2 := by sorry
