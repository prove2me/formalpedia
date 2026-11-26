-- Prove2me | Theorems.Thm_N4Code_dRowMin_union
-- name    : N4Code.dRowMin_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:10:28.15038+00:00
-- url     : https://prove2.me/theorems/005384ab-cb9a-5cf0-881d-6c9da54e0f6a
-- title:
--   N4 Code: d Row Min union
-- statement:
--   The minimum over S ∪ T is the min of the two minima.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L48-L54
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L48-L54

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.dRowMin_union {n : ℕ} (C : Code n) (S T : Finset (Fin 4)) (hS : S.Nonempty)
    (hT : T.Nonempty) (y : Word n) :
    dRowMin C (S ∪ T) (by rcases hS with ⟨i, hi⟩; exact ⟨i, Finset.mem_union_left T hi⟩) y =
      min (dRowMin C S hS y) (dRowMin C T hT y) := by sorry
