-- Prove2me | Theorems.Thm_N4Code_even_le_odd_succ
-- name    : N4Code.even_le_odd_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:21:48.193407+00:00
-- url     : https://prove2.me/theorems/e5b02a4a-4742-5c61-938f-3087d9362646
-- title:
--   N4 Code: even le odd succ
-- statement:
--   An even number at most an odd number is at most the even number one
--   smaller (2a ≤ 2b+1 sharpens to 2a+1 ≤ 2b+1).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L2178-L2183
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L2178-L2183

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.even_le_odd_succ {a b : ℕ} (h : 2 * a ≤ 2 * b + 1) : 2 * a + 1 ≤ 2 * b + 1 := by sorry
