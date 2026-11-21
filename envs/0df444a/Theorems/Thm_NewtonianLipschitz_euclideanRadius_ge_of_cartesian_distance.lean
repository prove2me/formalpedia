-- Prove2me | Theorems.Thm_NewtonianLipschitz_euclideanRadius_ge_of_cartesian_distance
-- name    : NewtonianLipschitz.euclideanRadius_ge_of_cartesian_distance
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:26:05.701324+00:00
-- url     : https://prove2.me/theorems/624245e8-8208-4634-8f0a-23033fd18b7f
-- title:
--   Newtonian Lipschitz: euclidean Radius ge of cartesian distance
-- statement:
--   A positive lower distance certificate stated in
--   the Cartesian/Pi norm, implies the *Euclidean* lower radius that is
--   actually used in the inverse-cube denominator.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Norms.lean#L30-L37
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/Norms.lean#L30-L37

module
public import Definitions.Def_NewtonianLipschitz_Basic
public import Definitions.Def_NewtonianLipschitz_Norms
set_option autoImplicit true
@[expose] public section
public section
open scoped NNReal Topology InnerProductSpace
open NewtonianLipschitz

theorem NewtonianLipschitz.euclideanRadius_ge_of_cartesian_distance
    (x : Vec3) (d : ℝ)
    (hclear : d ≤ dist x (0 : Vec3)) :
    d ≤ euclideanRadius x := by sorry
