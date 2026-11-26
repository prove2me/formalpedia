-- Prove2me | Theorems.Thm_N4Code_hammingDist_row_eq_indicator
-- name    : N4Code.hammingDist_row_eq_indicator
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:57:16.681863+00:00
-- url     : https://prove2.me/theorems/e3d0b637-59e3-48d5-9017-bf19844a9087
-- title:
--   N4 Code: hamming Dist row eq indicator
-- statement:
--   A row distance is the sum of the per-column test-bit mismatches.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L166-L172
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L166-L172

import Definitions.Def_N4Code_Definitions
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Definitions.Def_N4Code_Basic
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000
open N4Code

theorem N4Code.hammingDist_row_eq_indicator {n : ℕ} (C : Code n) (i j : Fin 4) :
    hammingDist (row C i) (row C j) =
      ∑ t : Fin n, if (colVal (C t)).testBit (3 - i.val) ≠ (colVal (C t)).testBit (3 - j.val) then 1 else 0 := by sorry
