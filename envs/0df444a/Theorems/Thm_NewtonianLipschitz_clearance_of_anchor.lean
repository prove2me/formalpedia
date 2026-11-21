-- Prove2me | Theorems.Thm_NewtonianLipschitz_clearance_of_anchor
-- name    : NewtonianLipschitz.clearance_of_anchor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:31:25.679657+00:00
-- url     : https://prove2.me/theorems/b322bd89-32dc-4d47-b631-b7095eb385fe
-- title:
--   Newtonian Lipschitz: clearance of anchor
-- statement:
--   Clearance at a displaced point from a nominal geometric anchor.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Clearance.lean#L18-L38
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Clearance.lean#L18-L38

module
public import Definitions.Def_NewtonianLipschitz_Norms
public import Definitions.Def_NewtonianLipschitz_Clearance
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.clearance_of_anchor
    (anchor center x : Vec3) (ε ρ d : ℝ)
    (hd : 0 < d)
    (hx : dist x center < ρ)
    (hcenter : dist center anchor ≤ ε)
    (hanchor : d + ε + ρ ≤ dist anchor (0 : Vec3)) :
    d ≤ dist x (0 : Vec3) ∧ x ≠ 0 := by sorry
