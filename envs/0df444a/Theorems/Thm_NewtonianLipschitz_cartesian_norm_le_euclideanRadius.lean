-- Prove2me | Theorems.Thm_NewtonianLipschitz_cartesian_norm_le_euclideanRadius
-- name    : NewtonianLipschitz.cartesian_norm_le_euclideanRadius
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:22:46.37018+00:00
-- url     : https://prove2.me/theorems/9ed1ad2f-d843-453f-a9f9-5cf113fd8694
-- title:
--   Newtonian Lipschitz: cartesian norm le euclidean Radius
-- statement:
--   The Newtonian Lipschitz construction uses the cartesian norm le euclidean Radius property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Norms.lean#L19-L25
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Norms.lean#L19-L25

module
public import Definitions.Def_NewtonianLipschitz_Basic
public import Definitions.Def_NewtonianLipschitz_Norms
set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz

theorem NewtonianLipschitz.cartesian_norm_le_euclideanRadius (x : Vec3) :
    ‖x‖ ≤ euclideanRadius x := by sorry
