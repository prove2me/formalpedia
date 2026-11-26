-- Prove2me | Theorems.Thm_N4Code_not_odd_of_even
-- name    : N4Code.not_odd_of_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:21:51.877745+00:00
-- url     : https://prove2.me/theorems/e5350770-64cc-5cae-8ff8-b6572de67a90
-- title:
--   N4 Code: not odd of even
-- statement:
--   An even number is not odd.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L2208-L2211
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L2208-L2211

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.not_odd_of_even {a : ℕ} (h : Even a) : ¬ Odd a := by sorry
