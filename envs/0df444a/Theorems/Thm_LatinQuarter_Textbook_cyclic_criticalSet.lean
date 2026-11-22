-- Prove2me | Theorems.Thm_LatinQuarter_Textbook_cyclic_criticalSet
-- name    : LatinQuarter.Textbook.cyclic_criticalSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:23:32.448547+00:00
-- url     : https://prove2.me/theorems/10981b6e-e2d4-432a-98ee-1a953e0b30b3
-- title:
--   Textbook: cyclic critical Set
-- statement:
--   The two corner triangles of `B_n` form a critical set of size `⌊n²/4⌋`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Textbook.lean#L200-L242
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Textbook.lean#L200-L242

module
public import Mathlib.SetTheory.Cardinal.Finite
public import Definitions.Def_LeanPool_LatinQuarter_Main
public import Definitions.Def_LeanPool_LatinQuarter_Parity
public import Definitions.Def_LeanPool_LatinQuarter_Textbook
set_option autoImplicit true
@[expose] public section
public section
open LatinQuarter LatinQuarter.Textbook

theorem LatinQuarter.Textbook.cyclic_criticalSet (n : ℕ) (hn : 0 < n) :
    ∃ T, CriticalSet (cyclicSquare n) T ∧ T.card = n * n / 4 := by sorry
