-- Prove2me | Theorems.Thm_NewtonianLipschitz_lateralRowNumerator_le_dominant
-- name    : NewtonianLipschitz.lateralRowNumerator_le_dominant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:26:19.788026+00:00
-- url     : https://prove2.me/theorems/3dca52c5-a2d9-49b9-9e6c-934ddad66456
-- title:
--   Newtonian Lipschitz: lateral Row Numerator le dominant
-- statement:
--   The row indexed by a maximal absolute Cartesian coordinate dominates
--   a lateral row, in the normalized positive octant.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianRows.lean#L45-L65
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianRows.lean#L45-L65

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_JacobianRows
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.lateralRowNumerator_le_dominant
    (u v : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    lateralRowNumerator u v ≤ dominantRowNumerator u v := by sorry
