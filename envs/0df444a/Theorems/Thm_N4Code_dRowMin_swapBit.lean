-- Prove2me | Theorems.Thm_N4Code_dRowMin_swapBit
-- name    : N4Code.dRowMin_swapBit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:14:48.3412+00:00
-- url     : https://prove2.me/theorems/573031a4-b744-5d59-887e-175f8cc5aef7
-- title:
--   N4 Code: d Row Min swap Bit
-- statement:
--   The minimum over S is unchanged when swapping two zero-column bits.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2387-L2395
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2387-L2395

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.dRowMin_swapBit {n : ℕ} (C : Code n) (S : Finset (Fin 4)) (hS : S.Nonempty)
    (t₁ t' : Fin n) (h1 : C t₁ = col0) (h' : C t' = col0) (y : Word n) :
    dRowMin C S hS (swapBits t₁ t' y) = dRowMin C S hS y := by sorry
