-- Prove2me | Theorems.Thm_N4Code_hammingDist_eq_zero_iff
-- name    : N4Code.hammingDist_eq_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:58:22.8466+00:00
-- url     : https://prove2.me/theorems/fe43281b-a245-47f0-900a-2cfac23d6835
-- title:
--   N4 Code: hamming Dist eq zero iff
-- statement:
--   Hamming distance is zero iff the words are equal.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L87-L96
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L87-L96

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

theorem N4Code.hammingDist_eq_zero_iff {n : ℕ} (x y : Word n) : hammingDist x y = 0 ↔ x = y := by sorry
