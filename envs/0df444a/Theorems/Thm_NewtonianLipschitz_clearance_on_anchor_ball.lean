-- Prove2me | Theorems.Thm_NewtonianLipschitz_clearance_on_anchor_ball
-- name    : NewtonianLipschitz.clearance_on_anchor_ball
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:31:21.807317+00:00
-- url     : https://prove2.me/theorems/c2fdae31-9f7b-487c-9313-cbe37d045ee6
-- title:
--   Newtonian Lipschitz: clearance on anchor ball
-- statement:
--   Clearance from an anchor's radius extends to a whole ball.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Clearance.lean#L41-L49
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Clearance.lean#L41-L49

module
public import Definitions.Def_NewtonianLipschitz_Norms
public import Definitions.Def_NewtonianLipschitz_Clearance
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.clearance_on_anchor_ball
    (anchor : Vec3) (ρ d : ℝ)
    (hd : 0 < d) (hanchor : d + ρ ≤ dist anchor (0 : Vec3)) :
    ∀ x ∈ Metric.ball anchor ρ, d ≤ euclideanRadius x := by sorry
