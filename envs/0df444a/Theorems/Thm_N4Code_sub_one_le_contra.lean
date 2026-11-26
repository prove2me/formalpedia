-- Prove2me | Theorems.Thm_N4Code_sub_one_le_contra
-- name    : N4Code.sub_one_le_contra
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:21:53.925941+00:00
-- url     : https://prove2.me/theorems/bb9866b1-3e05-436f-bc59-7e8512c0297d
-- title:
--   N4 Code: sub one le contra
-- statement:
--   b−1 ≤ a ≤ b−2 with b ≥ 2 is impossible.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L2230-L2231
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L2230-L2231

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.sub_one_le_contra {a b : ℕ} (h1 : b - 1 ≤ a) (h2 : a ≤ b - 2) (hb : 2 ≤ b) : False := by sorry
