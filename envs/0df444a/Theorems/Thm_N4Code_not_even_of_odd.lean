-- Prove2me | Theorems.Thm_N4Code_not_even_of_odd
-- name    : N4Code.not_even_of_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:29:31.560933+00:00
-- url     : https://prove2.me/theorems/d89031da-41df-47f2-a4ba-6ed99092155c
-- title:
--   N4 Code: not even of odd
-- statement:
--   An odd number is not even.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L2202-L2205
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L2202-L2205

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.not_even_of_odd {a : ℕ} (h : Odd a) : ¬ Even a := by sorry
