-- Prove2me | Theorems.Thm_N4Code_colVal_colOfNat
-- name    : N4Code.colVal_colOfNat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:53:34.131372+00:00
-- url     : https://prove2.me/theorems/4132de68-653e-4402-a11d-fe2c6547d3ee
-- title:
--   N4 Code: col Val col Of Nat
-- statement:
--   The type number of `colOfNat k` is `k`, for `k ≤ 15`.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Definitions.lean#L405-L406
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Definitions.lean#L405-L406

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

theorem N4Code.colVal_colOfNat (k : ℕ) (hk : k ≤ 15) : colVal (colOfNat k) = k := by sorry
