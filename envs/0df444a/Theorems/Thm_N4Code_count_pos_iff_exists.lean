-- Prove2me | Theorems.Thm_N4Code_count_pos_iff_exists
-- name    : N4Code.count_pos_iff_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:59:37.053989+00:00
-- url     : https://prove2.me/theorems/5e82d6ba-72cd-4132-b9a0-ab82e094ad7e
-- title:
--   N4 Code: count pos iff exists
-- statement:
--   A positive count of type-i columns means some column has that type.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L377-L396
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L377-L396

import Definitions.Def_N4Code_Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_Performance
set_option autoImplicit true
open scoped BigOperators
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.count_pos_iff_exists {n : ℕ} (C : Code n) (i : ℕ) :
    count C i > 0 ↔ ∃ t : Fin n, colVal (C t) = i := by sorry
