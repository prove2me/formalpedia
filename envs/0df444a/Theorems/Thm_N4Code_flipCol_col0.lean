-- Prove2me | Theorems.Thm_N4Code_flipCol_col0
-- name    : N4Code.flipCol_col0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:24:38.329949+00:00
-- url     : https://prove2.me/theorems/6c499fcd-a994-59df-be8c-37b88bc833b7
-- title:
--   N4 Code: flip Col col0
-- statement:
--   Flipping the zero column gives the all-ones column.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2219-L2221
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2219-L2221

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.flipCol_col0 : flipCol col0 = col15 := by sorry
