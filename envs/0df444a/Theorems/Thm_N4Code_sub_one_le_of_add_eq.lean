-- Prove2me | Theorems.Thm_N4Code_sub_one_le_of_add_eq
-- name    : N4Code.sub_one_le_of_add_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:21:34.601937+00:00
-- url     : https://prove2.me/theorems/abd864e0-4b0d-4787-8345-03fcfb19b1a9
-- title:
--   N4 Code: sub one le of add eq
-- statement:
--   a + c = b with c ≤ 1 implies b − 1 ≤ a.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1666-L1667
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1666-L1667

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.sub_one_le_of_add_eq {a b c : ℕ} (h : a + c = b) (hc : c ≤ 1) : b - 1 ≤ a := by sorry
