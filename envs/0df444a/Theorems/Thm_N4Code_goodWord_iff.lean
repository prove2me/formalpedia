-- Prove2me | Theorems.Thm_N4Code_goodWord_iff
-- name    : N4Code.goodWord_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:56:29.997805+00:00
-- url     : https://prove2.me/theorems/f5a7d1bc-677d-4f12-9773-410aa4d6f188
-- title:
--   N4 Code: good Word iff
-- statement:
--   A word is good iff all its per-type weights match.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L396-L399
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L396-L399

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

theorem N4Code.goodWord_iff {n : ℕ} (C : Code n) (k : ℕ → ℕ) (y : Word n) :
    y ∈ GoodWords C k ↔ ∀ i ∈ Finset.Icc 0 15, w_i C i y = k i := by sorry
