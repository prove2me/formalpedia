-- Prove2me | Theorems.Thm_N4Code_colVal_flipCol
-- name    : N4Code.colVal_flipCol
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:16:05.188897+00:00
-- url     : https://prove2.me/theorems/8e645078-a536-47e4-9adc-d65b6fb68e14
-- title:
--   N4 Code: col Val flip Col
-- statement:
--   Flipping all bits of a column complements the type number.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2459-L2472
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2459-L2472

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.colVal_flipCol (c : Column) : colVal (flipCol c) = 15 - colVal c := by sorry
