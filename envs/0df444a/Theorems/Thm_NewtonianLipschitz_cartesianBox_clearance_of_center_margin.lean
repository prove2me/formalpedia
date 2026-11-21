-- Prove2me | Theorems.Thm_NewtonianLipschitz_cartesianBox_clearance_of_center_margin
-- name    : NewtonianLipschitz.cartesianBox_clearance_of_center_margin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:37:18.413581+00:00
-- url     : https://prove2.me/theorems/1f3bd54a-f737-4d62-a3f1-01c1f80608b8
-- title:
--   Newtonian Lipschitz: cartesian Box clearance of center margin
-- statement:
--   A Cartesian open box with an explicit center-margin
--   certificate is uniformly separated from the point source.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/CartesianBoxSharp.lean#L26-L39
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/CartesianBoxSharp.lean#L26-L39

module
public import Definitions.Def_NewtonianLipschitz_ConvexSharp
public import Definitions.Def_NewtonianLipschitz_CartesianBoxSharp
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.cartesianBox_clearance_of_center_margin
    (anchor : Vec3) (ρ d : ℝ) (hd : 0 < d)
    (hmargin : d + ρ ≤ dist anchor (0 : Vec3)) :
    ∀ z ∈ Metric.ball anchor ρ, d ≤ ‖z‖ := by sorry
