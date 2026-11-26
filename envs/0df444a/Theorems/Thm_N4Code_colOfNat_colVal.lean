-- Prove2me | Theorems.Thm_N4Code_colOfNat_colVal
-- name    : N4Code.colOfNat_colVal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:53:33.484194+00:00
-- url     : https://prove2.me/theorems/8c256a6b-df29-5e18-b517-5b407cf10780
-- title:
--   N4 Code: col Of Nat col Val
-- statement:
--   Rebuilding a column from its type number recovers the column.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Definitions.lean#L400-L402
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Definitions.lean#L400-L402

import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_N4Code_Definitions
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.colOfNat_colVal (c : Column) : colOfNat (colVal c) = c := by sorry
