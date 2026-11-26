-- Prove2me | Theorems.Thm_N4Code_zero_column_strict_transfer
-- name    : N4Code.zero_column_strict_transfer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:15:59.030441+00:00
-- url     : https://prove2.me/theorems/021ebc67-a5c3-51d2-a1ca-f339352af1b0
-- title:
--   N4 Code: zero column strict transfer
-- statement:
--   Transfer a strict improvement from the normalized code back to the
--   original code at a common zero column.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2533-L2609
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2533-L2609

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.zero_column_strict_transfer {n : ℕ} (C C' : Code n) (ρ : Equiv (Fin 4) (Fin 4))
    (f : Fin n → Bool) (hh : ∀ u : Fin n, C' u = rowPermute ρ (if f u then flipCol (C u) else C u))
    (t : Fin n) (hcolC : C t = col0) (hcolC' : C' t = col0)
    (h : ∃ y : Word n, Y3c C' col5 colZeros_col5_nonempty colOnes_col5_nonempty t y) :
    ∃ s' : Column, (colVal s' = 3 ∨ colVal s' = 5 ∨ colVal s' = 6) ∧
      UniversalStrictBetter (replaceColumn C t s') C := by sorry
