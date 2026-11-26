-- Prove2me | Theorems.Thm_N4Code_min3_eq_middle_of_le
-- name    : N4Code.min3_eq_middle_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:21:17.443941+00:00
-- url     : https://prove2.me/theorems/2610e345-4ba8-577b-9fe9-31ed003351f8
-- title:
--   N4 Code: min3 eq middle of le
-- statement:
--   min a (min b c) = b when b ≤ a and b ≤ c.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1303-L1306
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1303-L1306

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.min3_eq_middle_of_le {a b c : ℕ} (ha : b ≤ a) (hc : b ≤ c) :
    min a (min b c) = b := by sorry
