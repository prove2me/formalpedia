-- Prove2me | Theorems.Thm_N4Code_odd_le_even_succ
-- name    : N4Code.odd_le_even_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:19:54.102147+00:00
-- url     : https://prove2.me/theorems/7e889cbc-da2e-5b9d-a609-b8ed855befeb
-- title:
--   N4 Code: odd le even succ
-- statement:
--   An odd number at most an even number is at most the even number one
--   smaller (2a+1 ≤ 2b sharpens to 2a+2 ≤ 2b).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L2187-L2191
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L2187-L2191

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.odd_le_even_succ {a b : ℕ} (h : 2 * a + 1 ≤ 2 * b) : 2 * a + 2 ≤ 2 * b := by sorry
