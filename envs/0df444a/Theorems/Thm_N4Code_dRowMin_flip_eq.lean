-- Prove2me | Theorems.Thm_N4Code_dRowMin_flip_eq
-- name    : N4Code.dRowMin_flip_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:10:01.108606+00:00
-- url     : https://prove2.me/theorems/a576e3ed-df37-4c7a-85cb-9408f8782588
-- title:
--   N4 Code: d Row Min flip eq
-- statement:
--   Flipping y at a zero column shifts the minimum over S by exactly ∓1.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L183-L225
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L183-L225

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.dRowMin_flip_eq {n : ℕ} (C : Code n) (S : Finset (Fin 4)) (hS : S.Nonempty)
    (t : Fin n) (y : Word n) (hcol : C t = col0) :
    (y t = true → dRowMin C S hS (flipBit t y) = dRowMin C S hS y - 1) ∧
      (y t = false → dRowMin C S hS (flipBit t y) = dRowMin C S hS y + 1) := by sorry
