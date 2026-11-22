-- Prove2me | Theorems.Thm_MasulloRH_localized_polar_and_real_density_annihilating_test
-- name    : MasulloRH.localized_polar_and_real_density_annihilating_test
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T12:40:09.057539+00:00
-- url     : https://prove2.me/theorems/c6c2b004-bc79-4563-98dd-b68c5f2a18ea
-- title:
--   Localized smooth prime probe annihilating the real-place density and both half-weight poles
-- statement:
--   In every positive log-radius interval there is a smooth real test supported in that interval, nonzero at its center, with Mellin moments zero at both half weights and at plus or minus one. Its integral against the real Euler density exp(a x)/(1-exp(-2x)) vanishes at a=-1/2,-3/2,1,-1. A differential moment filter preserves the support of a bump, then multiplication by (1-exp(-2x)) removes the density denominator. The center can be the logarithm of a selected prime, with the interval avoiding all other prime powers.
-- source:
--   Masullo mission: fixed prime probes for the positive-log archimedean geometric density; no trace comparison assumed.

import Mathlib
open MeasureTheory Set Filter Metric
open scoped Topology ContDiff

theorem MasulloRH.localized_polar_and_real_density_annihilating_test (c r : ℝ) (hr : 0 < r) (hc : r < c) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ tsupport f ⊆ closedBall c r ∧ f c ≠ 0 ∧
      (∀ a ∈ ([1/2, -1/2, 1, -1] : List ℝ), (∫ x : ℝ, Real.exp (a*x) * f x) = 0) ∧
      (∀ a ∈ ([-1/2, -3/2, 1, -1] : List ℝ),
        (∫ x : ℝ, Real.exp (a*x) * f x / (1 - Real.exp (-2*x))) = 0) := by sorry
