-- Prove2me | Theorems.Thm_N4Code_colBit_eq_testBit
-- name    : N4Code.colBit_eq_testBit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:53:31.074339+00:00
-- url     : https://prove2.me/theorems/15cf9b35-af06-54e5-b34c-899877ba955b
-- title:
--   N4 Code: col Bit eq test Bit
-- statement:
--   Bit j of a column equals bit `3 - j.val` of its type number (row 1 = MSB).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Definitions.lean#L392-L397
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Definitions.lean#L392-L397

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

theorem N4Code.colBit_eq_testBit (c : Column) (j : Fin 4) :
    colBit j c = (colVal c).testBit (3 - j.val) := by sorry
