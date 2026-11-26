-- Prove2me | Theorems.Thm_N4Code_min3_eq_of_gt
-- name    : N4Code.min3_eq_of_gt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:21:13.961223+00:00
-- url     : https://prove2.me/theorems/c4e490b5-e486-4495-ba5d-504a4dd2d9a9
-- title:
--   N4 Code: min3 eq of gt
-- statement:
--   If min a (min b c) = d with a,c > d, then b = d.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L986-L1002
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L986-L1002

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.min3_eq_of_gt {a b c d : ℕ} (ha : d < a) (hc : d < c) (hm : min a (min b c) = d) :
    b = d := by sorry
