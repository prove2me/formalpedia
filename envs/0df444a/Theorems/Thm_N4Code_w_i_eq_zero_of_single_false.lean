-- Prove2me | Theorems.Thm_N4Code_w_i_eq_zero_of_single_false
-- name    : N4Code.w_i_eq_zero_of_single_false
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:19:18.025433+00:00
-- url     : https://prove2.me/theorems/090284c5-1254-57eb-81ed-471be7b3bae0
-- title:
--   N4 Code: w i eq zero of single false
-- statement:
--   If |i| = 1 and the single type-i column has y = false, then w_i = 0.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L2154-L2174
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L2154-L2174

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.w_i_eq_zero_of_single_false {n : ℕ} (C : Code n) (i : ℕ) (t : Fin n) (y : Word n)
    (hcount : count C i = 1) (ht : colVal (C t) = i) (hyt : y t = false) :
    w_i C i y = 0 := by sorry
