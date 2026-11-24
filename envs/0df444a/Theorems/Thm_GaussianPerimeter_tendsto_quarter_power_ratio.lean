-- Prove2me | Theorems.Thm_GaussianPerimeter_tendsto_quarter_power_ratio
-- name    : GaussianPerimeter.tendsto_quarter_power_ratio
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T10:40:27.287631+00:00
-- url     : https://prove2.me/theorems/5afb7e8f-5f7d-42f9-b958-d1f95e7f1cb7
-- title:
--   Gaussian Perimeter: tendsto quarter power ratio
-- statement:
--   Replacing the dimension in the fourth root by its predecessor has no
--   effect in the limit.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Scaling.lean#L15-L35
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/GaussianPerimeter/Scaling.lean#L15-L35

module
public import Definitions.Def_GaussianPerimeter_Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Definitions.Def_GaussianPerimeter_Scaling
set_option autoImplicit true
@[expose] public section
public section
open Filter
open scoped Topology
open GaussianPerimeter

theorem GaussianPerimeter.tendsto_quarter_power_ratio :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ) / (n + 1 : ℝ) ^ (1 / 4 : ℝ))
      atTop (𝓝 1) := by sorry
