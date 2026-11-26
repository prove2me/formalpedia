-- Prove2me | Theorems.Thm_N4Code_hammingDist_rows_of_types
-- name    : N4Code.hammingDist_rows_of_types
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:58:34.78813+00:00
-- url     : https://prove2.me/theorems/5d385d20-ab6e-559e-83e9-83e5adeb8b72
-- title:
--   N4 Code: hamming Dist rows of types
-- statement:
--   The Hamming distance between rows i and j is the weighted sum of the counts
--   of the column types for which the i-th and j-th bits differ.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L200-L207
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L200-L207

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

theorem N4Code.hammingDist_rows_of_types {n : ℕ} (C : Code n) (i j : Fin 4)
    (S : Finset ℕ) (hS : ∀ t : Fin n, colVal (C t) ∈ S) :
    hammingDist (row C i) (row C j) =
      ∑ k ∈ S, count C k *
        if k.testBit (3 - i.val) ≠ k.testBit (3 - j.val) then 1 else 0 := by sorry
