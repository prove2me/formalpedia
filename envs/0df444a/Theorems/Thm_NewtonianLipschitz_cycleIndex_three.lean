-- Prove2me | Theorems.Thm_NewtonianLipschitz_cycleIndex_three
-- name    : NewtonianLipschitz.cycleIndex_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:29:30.806192+00:00
-- url     : https://prove2.me/theorems/256503d1-6aa0-4bd2-973e-a1f10f3a2bbd
-- title:
--   Newtonian Lipschitz: cycle Index three
-- statement:
--   Three cyclic relabelings return every Cartesian index to itself.
--   Proved where the defining equation of cycleIndex is available.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianPermutations.lean#L33-L35
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianPermutations.lean#L33-L35

module
public import Definitions.Def_NewtonianLipschitz_JacobianSymmetries
public import Definitions.Def_NewtonianLipschitz_JacobianPermutations
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.cycleIndex_three (i : Fin 3) :
    cycleIndex (cycleIndex (cycleIndex i)) = i := by sorry
