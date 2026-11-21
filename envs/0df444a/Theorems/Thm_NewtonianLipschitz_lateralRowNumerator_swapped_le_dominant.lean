-- Prove2me | Theorems.Thm_NewtonianLipschitz_lateralRowNumerator_swapped_le_dominant
-- name    : NewtonianLipschitz.lateralRowNumerator_swapped_le_dominant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:32:00.603474+00:00
-- url     : https://prove2.me/theorems/8f51988a-cf6f-402f-9828-0b1e6b3d7d66
-- title:
--   Newtonian Lipschitz: lateral Row Numerator swapped le dominant
-- statement:
--   The third row enjoys the same bound, with u and v exchanged.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianRows.lean#L68-L77
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/JacobianRows.lean#L68-L77

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_JacobianRows
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.lateralRowNumerator_swapped_le_dominant
    (u v : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    lateralRowNumerator v u ≤ dominantRowNumerator u v := by sorry
