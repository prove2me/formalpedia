-- Prove2me | Theorems.Thm_N4Code_sub_two_lt_sub_one
-- name    : N4Code.sub_two_lt_sub_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:21:38.997803+00:00
-- url     : https://prove2.me/theorems/5eab5d89-78c0-5f66-85d8-4478eb2a51d6
-- title:
--   N4 Code: sub two lt sub one
-- statement:
--   a ≥ 2 gives a − 2 < a − 1.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1673-L1673
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1673-L1673

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.sub_two_lt_sub_one {a : ℕ} (h : 2 ≤ a) : a - 2 < a - 1 := by sorry
