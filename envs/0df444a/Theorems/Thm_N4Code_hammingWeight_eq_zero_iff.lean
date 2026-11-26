-- Prove2me | Theorems.Thm_N4Code_hammingWeight_eq_zero_iff
-- name    : N4Code.hammingWeight_eq_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:56:52.887951+00:00
-- url     : https://prove2.me/theorems/fac0eb6e-c463-4d69-bcd8-059775638dda
-- title:
--   N4 Code: hamming Weight eq zero iff
-- statement:
--   A word has weight zero iff it is the zero word.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L65-L75
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L65-L75

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

theorem N4Code.hammingWeight_eq_zero_iff {n : ℕ} (w : Word n) :
    hammingWeight w = 0 ↔ ∀ i : Fin n, w i = false := by sorry
