-- Prove2me | Theorems.Thm_N4Code_dRow_swapBit
-- name    : N4Code.dRow_swapBit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:14:44.1468+00:00
-- url     : https://prove2.me/theorems/90e1bd09-8ea3-5f6b-83a6-3457a9396d37
-- title:
--   N4 Code: d Row swap Bit
-- statement:
--   Swapping two bits of a word preserves every row distance when the two
--   positions hold zero columns.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2372-L2384
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2372-L2384

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.dRow_swapBit {n : ℕ} (C : Code n) (j : Fin 4) (t₁ t' : Fin n)
    (h1 : C t₁ = col0) (h' : C t' = col0) (y : Word n) :
    dRow C j (swapBits t₁ t' y) = dRow C j y := by sorry
