-- Prove2me | Theorems.Thm_N4Code_exists_weight1_of_count1_pos
-- name    : N4Code.exists_weight1_of_count1_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:59:37.123624+00:00
-- url     : https://prove2.me/theorems/c28e2d00-0257-4a49-bad6-b5c2e157cf2a
-- title:
--   N4 Code: exists weight1 of count1 pos
-- statement:
--   A code with a positive |1| has a weight-1 column.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L400-L405
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L400-L405

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

theorem N4Code.exists_weight1_of_count1_pos {n : ℕ} (C : Code n) (hpos : count C 1 > 0) :
    ∃ t : Fin n, colWeight (C t) = 1 := by sorry
