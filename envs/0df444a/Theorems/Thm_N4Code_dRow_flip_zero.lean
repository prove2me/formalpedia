-- Prove2me | Theorems.Thm_N4Code_dRow_flip_zero
-- name    : N4Code.dRow_flip_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:11:56.287869+00:00
-- url     : https://prove2.me/theorems/1e813b95-6b2f-5435-a02e-7ceffec680ed
-- title:
--   N4 Code: d Row flip zero
-- statement:
--   Flipping y at t, where the column at t is all zeros, changes each row
--   distance by exactly ∓1.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L88-L141
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L88-L141

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.dRow_flip_zero {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) (hcol : C t = col0) :
    ∀ i : Fin 4, (y t = true → dRow C i (flipBit t y) = dRow C i y - 1) ∧
      (y t = false → dRow C i (flipBit t y) = dRow C i y + 1) := by sorry
