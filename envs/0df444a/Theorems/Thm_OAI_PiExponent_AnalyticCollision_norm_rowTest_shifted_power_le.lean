-- Prove2me | Theorems.Thm_OAI_PiExponent_AnalyticCollision_norm_rowTest_shifted_power_le
-- name    : OAI.PiExponent.AnalyticCollision.norm_rowTest_shifted_power_le
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T05:00:05.884131+00:00
-- url     : https://prove2.me/theorems/1770b982-7f71-44cd-b722-e217f9821b2b
-- title:
--   Coefficient bound for shifted logarithmic powers
-- statement:
--   On the half-radius circle, the shifted logarithmic argument divided by R has norm at most 1/2; applying the row Cauchy coefficient estimate gives the stated power bound. The center margin `3/4` is used with the logarithm estimate at `‖t‖ = 1/2`; the estimate also covers `d = 0` and `ell = 0`.

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Log
open Filter Topology

theorem OAI.PiExponent.AnalyticCollision.norm_rowTest_shifted_power_le {center : ℂ} {R : ℝ} (hR : 0 < R) (hc : ‖center‖ + 3 / 4 ≤ R / 2) (ell d : ℕ) : ‖cauchyPowerSeries (fun t : ℂ => (((center + Complex.log (1 + t)) / (R : ℂ)) ^ d)) 0 (1 / 2) ell (fun _ => (1 : ℂ))‖ ≤ (2 : ℝ) ^ ell * (1 / 2 : ℝ) ^ d := by sorry
