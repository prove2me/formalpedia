-- Prove2me | Theorems.Thm_MasulloRH_two_point_weighted_riesz_profile_discriminator
-- name    : MasulloRH.two_point_weighted_riesz_profile_discriminator
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T05:30:06.817601+00:00
-- url     : https://prove2.me/theorems/76dc2eb2-8e53-40b7-bfe4-142861d623a2
-- title:
--   An explicit two-point test detects distortion of the weighted Riesz profile for positive-norm inputs
-- statement:
--   For $w(x)=e^{2α|x|}(1+x²)^2$, $α≥0$, and a nonzero nonnegative continuous compact input $h$ vanishing for $y≤0$, the response $w(x)∫h(y)/w(x-y)dy$ is strictly greater at $x=1$ than at $x=-1$. This covers every one-sided positive bump, and a critical-line Riesz input after a compensating character phase.
-- source:
--   Masullo (9.2.2.41) and (11.2.1.4); explicit test used in the rational cross-block argument.

import Mathlib
open MeasureTheory

theorem MasulloRH.two_point_weighted_riesz_profile_discriminator (α : ℝ) (hα : 0 ≤ α) (h : ℝ → ℝ)
    (hc : Continuous h) (hcs : HasCompactSupport h) (hn : ∀ y, 0 ≤ h y)
    (hs : ∀ y ≤ 0, h y = 0) (hp : ∃ y, 0 < h y) :
    let w : ℝ → ℝ := fun x => Real.exp (2*α*|x|) * (1+x^2)^2
    w (-1) * (∫ y : ℝ, h y / w (-1-y)) <
      w 1 * (∫ y : ℝ, h y / w (1-y)) := by sorry
