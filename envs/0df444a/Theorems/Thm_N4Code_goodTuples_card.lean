-- Prove2me | Theorems.Thm_N4Code_goodTuples_card
-- name    : N4Code.goodTuples_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:57:46.615794+00:00
-- url     : https://prove2.me/theorems/dcf8373b-f73c-4e88-aa05-f153deed7ea3
-- title:
--   N4 Code: good Tuples card
-- statement:
--   The number of good tuples is the product of binomials.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L517-L571
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L517-L571

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

theorem N4Code.goodTuples_card {n : ℕ} (C : Code n) (k : ℕ → ℕ) :
    (GoodTuples C k).card = ∏ i ∈ Finset.Icc 0 15, Nat.choose (count C i) (k i) := by sorry
