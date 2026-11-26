-- Prove2me | Theorems.Thm_N4Code_w_i_eq_of_single
-- name    : N4Code.w_i_eq_of_single
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:19:16.090884+00:00
-- url     : https://prove2.me/theorems/3298ea24-22e9-5d4c-bf37-dacda665a827
-- title:
--   N4 Code: w i eq of single
-- statement:
--   If |i| = 1 and the single type-i column has y = true, then w_i = 1.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L2131-L2151
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L2131-L2151

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.w_i_eq_of_single {n : ℕ} (C : Code n) (i : ℕ) (t : Fin n) (y : Word n)
    (hcount : count C i = 1) (ht : colVal (C t) = i) (hyt : y t = true) :
    w_i C i y = 1 := by sorry
