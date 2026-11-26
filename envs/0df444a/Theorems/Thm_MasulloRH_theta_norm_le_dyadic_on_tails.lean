-- Prove2me | Theorems.Thm_MasulloRH_theta_norm_le_dyadic_on_tails
-- name    : MasulloRH.theta_norm_le_dyadic_on_tails
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T09:48:04.944771+00:00
-- url     : https://prove2.me/theorems/4fc48a8d-7b85-5f54-883e-2b08fff585f7
-- title:
--   A uniform dyadic norm bound on both tails of the logarithmic Gaussian theta sum
-- statement:
--   For the canonical complex-valued logarithmic Gaussian theta sum, \(\lVert\theta(x)\rVert\le 2^{-64}\) throughout the two closed half-lines \(x\le-3\) and \(x\ge3/2\). One enclosure with rational center zero and rational radius \(2^{-64}\) therefore covers every translated height-two grid cell wholly inside either half-line.
-- source:
--   The explicit rational witness is https://prove2.me/definitions/d1967a7a-bf7f-42bd-8ad5-820a7680a39d . This is a component of https://prove2.me/theorems/a1982f8d-9d4a-4b3f-88ac-3a2cdaee2ead .

import Definitions.Def_MasulloRH_GaussianThetaApproximation

open MasulloRH.GaussianApproximation

theorem MasulloRH.theta_norm_le_dyadic_on_tails (x : ℝ) (hx : x ≤ -3 ∨ 3/2 ≤ x) :
    ‖theta x‖ ≤ 1/(2:ℝ)^64 := by sorry
