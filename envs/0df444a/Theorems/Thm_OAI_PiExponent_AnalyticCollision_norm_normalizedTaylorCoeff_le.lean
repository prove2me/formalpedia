-- Prove2me | Theorems.Thm_OAI_PiExponent_AnalyticCollision_norm_normalizedTaylorCoeff_le
-- name    : OAI.PiExponent.AnalyticCollision.norm_normalizedTaylorCoeff_le
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T04:59:21.580547+00:00
-- url     : https://prove2.me/theorems/f8a0a1f8-f45a-4841-8c9d-0cf22c1665a4
-- title:
--   Cauchy bound for normalized Taylor coefficients
-- statement:
--   A holomorphic function bounded by D on the radius-R circle has normalized Taylor coefficients bounded by D. The child can be proved from `cauchyPowerSeries_apply` and the norm bound for the circle integral. Its radius condition is strict positivity; the boundary estimate is exactly the hypothesis used by the integral estimate.

import Mathlib.Analysis.Complex.CauchyIntegral
open Filter Topology

theorem OAI.PiExponent.AnalyticCollision.norm_normalizedTaylorCoeff_le {f : ℂ → ℂ} {R D : ℝ} (hR : 0 < R) (hD : ∀ z, z ∈ Metric.sphere (0 : ℂ) R → ‖f z‖ ≤ D) (d : ℕ) : ‖cauchyPowerSeries f 0 R d (fun _ => (R : ℂ))‖ ≤ D := by sorry
