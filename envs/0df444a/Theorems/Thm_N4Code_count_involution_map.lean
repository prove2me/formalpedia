-- Prove2me | Theorems.Thm_N4Code_count_involution_map
-- name    : N4Code.count_involution_map
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:58:40.626727+00:00
-- url     : https://prove2.me/theorems/b174e730-6093-5c63-9064-334b24950ed7
-- title:
--   N4 Code: count involution map
-- statement:
--   Counts transport across an involutive type relabelling: if `colVal (C' t)`
--   is the image of `colVal (C t)` under the involution `gv`, then `|i|_{C'}` is
--   the count of `gv i` in `C`.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L212-L230
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L212-L230

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

theorem N4Code.count_involution_map {n : ℕ} (C C' : Code n) (gv : ℕ → ℕ)
    (hcol : ∀ t : Fin n, colVal (C' t) = gv (colVal (C t)))
    (hIdem : ∀ i : ℕ, gv (gv i) = i) (i : ℕ) :
    count C' i = count C (gv i) := by sorry
