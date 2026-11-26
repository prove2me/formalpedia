-- Prove2me | Theorems.Thm_N4Code_even_le_odd
-- name    : N4Code.even_le_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:19:55.828174+00:00
-- url     : https://prove2.me/theorems/04f14e48-d7cc-4469-9fad-e69bb3be2258
-- title:
--   N4 Code: even le odd
-- statement:
--   An even number at most an odd number is at most the even number itself
--   (2a ≤ 2b+1 sharpens to 2a ≤ 2b).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L2195-L2199
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L2195-L2199

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.even_le_odd {a b : ℕ} (h : 2 * a ≤ 2 * b + 1) : 2 * a ≤ 2 * b := by sorry
