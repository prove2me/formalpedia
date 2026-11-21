-- Prove2me | Theorems.Thm_NewtonianLipschitz_diagonalParameter_mem_unitInterval
-- name    : NewtonianLipschitz.diagonalParameter_mem_unitInterval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:32:54.572394+00:00
-- url     : https://prove2.me/theorems/7462b421-343d-489e-9212-7fb92b529720
-- title:
--   Newtonian Lipschitz: diagonal Parameter mem unit Interval
-- statement:
--   The diagonal parameter associated with two normalized Cartesian
--   coordinates lies in the unit interval.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/NormalizedSharpBound.lean#L21-L32
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/NormalizedSharpBound.lean#L21-L32

module
public import Definitions.Def_NewtonianLipschitz_JacobianMatrix
public import Definitions.Def_NewtonianLipschitz_ScalarMaximum
public import Definitions.Def_NewtonianLipschitz_NormalizedSharpBound
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.diagonalParameter_mem_unitInterval
    (u v : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    diagonalParameter u v ∈ Set.Icc (0 : ℝ) 1 := by sorry
