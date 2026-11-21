-- Prove2me | Theorems.Thm_NewtonianLipschitz_stationaryCubic_existsUnique_root_bracket
-- name    : NewtonianLipschitz.stationaryCubic_existsUnique_root_bracket
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:40:18.976108+00:00
-- url     : https://prove2.me/theorems/d5e3e485-5f98-4e3b-8197-2a9e9c12cf16
-- title:
--   Newtonian Lipschitz: stationary Cubic exists Unique root bracket
-- statement:
--   Uniqueness of the root in the exact rational bracket.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/CubicCandidate.lean#L133-L141
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/CubicCandidate.lean#L133-L141

module
public import Mathlib
public import Definitions.Def_NewtonianLipschitz_CubicCandidate
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.stationaryCubic_existsUnique_root_bracket :
    ∃! t : ℝ, (9 / 50 : ℝ) ≤ t ∧ t ≤ 1 / 5 ∧
      stationaryCubic t = 0 := by sorry
