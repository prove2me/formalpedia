-- Prove2me | Theorems.Thm_GJKKL_Trajectory_trend_upper
-- name    : GJKKL.Trajectory.trend_upper
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:52:48.646935+00:00
-- url     : https://prove2.me/theorems/fa870ab8-0a55-48cc-a1f6-e693aa22c941
-- title:
--   Trajectory: trend upper
-- statement:
--   Trend of the upper process.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Trend.lean#L27-L72
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Trend.lean#L27-L72

module
public import Mathlib
public import Definitions.Def_GJKKL_Trajectory_Trend
set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Trajectory

theorem GJKKL.Trajectory.trend_upper {K1 κ c B dh δ aP Asz D loss g r : ℝ} (hK1 : 0 ≤ K1) (hκ : 0 ≤ κ)
    (hc : 0 ≤ c) (hdh : 0 < dh) (hδ0 : 0 ≤ δ) (hδ : δ ≤ dh / 2) (haP : 16 ≤ aP)
    (hDL : dh - δ ≤ D) (hDU : D ≤ dh + δ) (hAL : aP * (dh - δ) ≤ Asz)
    (hAU : Asz ≤ aP * (dh + δ)) (hDA : D ≤ Asz)
    (hloss : D * K1 * (dh - δ) - D * κ * c ≤ loss) (hg0 : 0 ≤ g) (hg : g ≤ K1 * dh / aP)
    (hr : B * δ / aP ≤ r) (hB : 32 * K1 ≤ B) (hBc : 8 * κ * c ≤ B * δ) :
    -loss + (Asz - D) * (g - r) ≤ 0 := by sorry
