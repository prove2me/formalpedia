-- Prove2me | Theorems.Thm_N4Code_le_succ_of_sub_one_le
-- name    : N4Code.le_succ_of_sub_one_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:21:44.799723+00:00
-- url     : https://prove2.me/theorems/67609e15-2a80-4d86-a1fc-c1801a5c4988
-- title:
--   N4 Code: le succ of sub one le
-- statement:
--   a − 1 ≤ b gives a ≤ b + 1.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1676-L1676
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1676-L1676

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.le_succ_of_sub_one_le {a b : ℕ} (h : a - 1 ≤ b) : a ≤ b + 1 := by sorry
