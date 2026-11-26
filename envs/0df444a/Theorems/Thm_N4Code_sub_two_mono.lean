-- Prove2me | Theorems.Thm_N4Code_sub_two_mono
-- name    : N4Code.sub_two_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:21:36.255752+00:00
-- url     : https://prove2.me/theorems/578bd9a4-90fd-4c45-b6b3-0af9fd8f668c
-- title:
--   N4 Code: sub two mono
-- statement:
--   Subtraction is monotone.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1670-L1670
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1670-L1670

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.sub_two_mono {a b : ℕ} (h : a ≤ b) : a - 2 ≤ b - 2 := by sorry
