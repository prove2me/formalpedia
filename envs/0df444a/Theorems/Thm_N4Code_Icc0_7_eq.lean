-- Prove2me | Theorems.Thm_N4Code_Icc0_7_eq
-- name    : N4Code.Icc0_7_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:13:34.0828+00:00
-- url     : https://prove2.me/theorems/61eaf032-e7f8-461f-aafb-ac2edc20320c
-- title:
--   N4 Code: Icc0 7 eq
-- statement:
--   The type range 0..7 splits into {0,5,6} and {1,2,3,4,7}.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1489-L1502
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1489-L1502

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.Icc0_7_eq : (Finset.Icc 0 7 : Finset ℕ) = {0, 5, 6} ∪ {1, 2, 3, 4, 7} := by sorry
