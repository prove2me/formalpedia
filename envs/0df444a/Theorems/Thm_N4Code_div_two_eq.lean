-- Prove2me | Theorems.Thm_N4Code_div_two_eq
-- name    : N4Code.div_two_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:22:29.557199+00:00
-- url     : https://prove2.me/theorems/38f6da90-59ec-49a3-ac9e-468badb41b71
-- title:
--   N4 Code: div two eq
-- statement:
--   n = 2k implies n / 2 = k.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1428-L1430
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1428-L1430

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.div_two_eq {n k : ℕ} (h : n = 2 * k) : n / 2 = k := by sorry
