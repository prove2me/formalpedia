-- Prove2me | Theorems.Thm_GJKKL_Trajectory_trend_lower
-- name    : GJKKL.Trajectory.trend_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:52:50.100173+00:00
-- url     : https://prove2.me/theorems/0d2b6e99-2bc5-44af-97b1-e47e1e029fa1
-- title:
--   Trajectory: trend lower
-- statement:
--   Trend of the lower process.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Trend.lean#L75-L139
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Trajectory/Trend.lean#L75-L139

module
public import Mathlib
public import Definitions.Def_GJKKL_Trajectory_Trend
set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Trajectory

theorem GJKKL.Trajectory.trend_lower {K1 K2 B dh δ aP Asz D loss g r : ℝ} (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (hdh : 0 < dh) (hδ0 : 0 ≤ δ) (hδ : δ ≤ dh / 2) (haP : 16 ≤ aP) (haPK2 : K2 ≤ aP)
    (hDU : D ≤ dh + δ) (hAL : aP * (dh - δ) ≤ Asz) (hD0 : 0 ≤ D)
    (hloss : loss ≤ D * K1 * (dh + δ)) (hg : K1 * dh / aP - K1 * K2 * dh / aP ^ 2 ≤ g)
    (hr : B * δ / aP ≤ r) (hB : 32 * K1 ≤ B) (hBn : 4 * K1 * (2 + K2) * dh ≤ B * δ * aP) :
    loss - (Asz - D) * (g + r) ≤ 0 := by sorry
