-- Prove2me | Theorems.Thm_NewtonianLipschitz_euclideanRadius_cycleVec
-- name    : NewtonianLipschitz.euclideanRadius_cycleVec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:34:31.108341+00:00
-- url     : https://prove2.me/theorems/8375dec9-63d1-4f15-8957-ba4266385f01
-- title:
--   Newtonian Lipschitz: euclidean Radius cycle Vec
-- statement:
--   The Euclidean source radius is invariant under cyclic relabeling.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianPermutations.lean#L45-L51
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianPermutations.lean#L45-L51

module
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
public import Definitions.Def_NewtonianLipschitz_JacobianPermutations
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.euclideanRadius_cycleVec (x : Vec3) :
    euclideanRadius (cycleVec x) = euclideanRadius x := by sorry
