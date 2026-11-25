-- Prove2me | Theorems.Thm_HiltonMilner_fwt_sh_lt
-- name    : HiltonMilner.fwt_sh_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:49:19.094596+00:00
-- url     : https://prove2.me/theorems/d3729b23-b5c1-4160-9a3c-719dbead99d7
-- title:
--   Hilton Milner: fwt sh lt
-- statement:
--   A shift that changes the family strictly decreases its weight.
--
--   Source: https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/Shift.lean#L163-L190
-- source:
--   https://github.com/jtraverso/hilton-milner/blob/6059a0d6f13378b9a92fba297f2d774598ee0f7d/HiltonMilnerLib/Shift.lean#L163-L190

module
public import Mathlib
public import Definitions.Def_HiltonMilnerLib_Shift
set_option autoImplicit true
@[expose] public section
public section
open Finset
open HiltonMilner

theorem HiltonMilner.fwt_sh_lt {y z : ℕ} (hyz : y < z) {𝒜 : Finset (Finset ℕ)} (hne : sh y z 𝒜 ≠ 𝒜) :
    fwt (sh y z 𝒜) < fwt 𝒜 := by sorry
