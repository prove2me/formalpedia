-- Prove2me | Theorems.Thm_N4Code_add_eq_le
-- name    : N4Code.add_eq_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:21:32.252308+00:00
-- url     : https://prove2.me/theorems/490a0b2d-3466-58ee-98cd-92ce1b972296
-- title:
--   N4 Code: add eq le
-- statement:
--   a + c = b implies a ≤ b.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1663-L1663
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1663-L1663

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.add_eq_le {a b c : ℕ} (h : a + c = b) : a ≤ b := by sorry
