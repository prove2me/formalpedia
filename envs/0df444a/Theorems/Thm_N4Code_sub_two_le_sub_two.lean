-- Prove2me | Theorems.Thm_N4Code_sub_two_le_sub_two
-- name    : N4Code.sub_two_le_sub_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:22:00.802178+00:00
-- url     : https://prove2.me/theorems/e9e676bc-7d3b-4b98-b167-f7716823c381
-- title:
--   N4 Code: sub two le sub two
-- statement:
--   a−2 ≤ b−2 with b ≥ 2 gives a ≤ b.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L2234-L2234
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L2234-L2234

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.sub_two_le_sub_two {a b : ℕ} (h : a - 2 ≤ b - 2) (hb : 2 ≤ b) : a ≤ b := by sorry
