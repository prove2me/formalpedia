-- Prove2me | Theorems.Thm_N4Code_dRow_C0_formula
-- name    : N4Code.dRow_C0_formula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:13:09.191258+00:00
-- url     : https://prove2.me/theorems/d457982d-5f20-4f7f-b686-537739d53ef9
-- title:
--   N4 Code: d Row C0 formula
-- statement:
--   The N4 Code construction uses the d Row C0 formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L636-L683
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L636-L683

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.dRow_C0_formula {n : ℕ} (C : Code n)
    (hC : ∀ u : Fin n, colVal (C u) = 0 ∨ colVal (C u) = 5 ∨ colVal (C u) = 6) :
    ∀ y : Word n,
      dRow C 0 y = w_i C 0 y + w_i C 5 y + w_i C 6 y ∧
      dRow C 1 y = w_i C 0 y + (count C 5 - w_i C 5 y) + (count C 6 - w_i C 6 y) ∧
      dRow C 2 y = w_i C 0 y + w_i C 5 y + (count C 6 - w_i C 6 y) ∧
      dRow C 3 y = w_i C 0 y + (count C 5 - w_i C 5 y) + w_i C 6 y := by sorry
