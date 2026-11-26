-- Prove2me | Theorems.Thm_N4Code_min3_le_of_gt
-- name    : N4Code.min3_le_of_gt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:29:44.08311+00:00
-- url     : https://prove2.me/theorems/a1631bbd-03e1-4378-9650-82705015f789
-- title:
--   N4 Code: min3 le of gt
-- statement:
--   If min a (min b c) ≤ d with a,c > d, then b ≤ d.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L2214-L2227
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L2214-L2227

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.min3_le_of_gt {a b c d : ℕ} (ha : d < a) (hc : d < c) (hm : min a (min b c) ≤ d) :
    b ≤ d := by sorry
