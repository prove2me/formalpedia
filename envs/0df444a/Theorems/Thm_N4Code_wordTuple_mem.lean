-- Prove2me | Theorems.Thm_N4Code_wordTuple_mem
-- name    : N4Code.wordTuple_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:57:44.512461+00:00
-- url     : https://prove2.me/theorems/c61e23f2-c122-4f6c-8816-937701dafde7
-- title:
--   N4 Code: word Tuple mem
-- statement:
--   A good word maps to a good tuple.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L451-L459
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L451-L459

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

theorem N4Code.wordTuple_mem {n : ℕ} (C : Code n) (k : ℕ → ℕ) {y : Word n} (hy : y ∈ GoodWords C k) :
    GoodTuplePred C k (wordTuple C y) := by sorry
