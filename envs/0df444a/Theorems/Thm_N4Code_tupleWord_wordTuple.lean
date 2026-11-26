-- Prove2me | Theorems.Thm_N4Code_tupleWord_wordTuple
-- name    : N4Code.tupleWord_wordTuple
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:57:29.115506+00:00
-- url     : https://prove2.me/theorems/9c206879-c715-59ce-b6d5-85cbec52d0b8
-- title:
--   N4 Code: tuple Word word Tuple
-- statement:
--   Rebuilding a word from its tuple recovers the word.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L473-L476
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L473-L476

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

theorem N4Code.tupleWord_wordTuple {n : ℕ} (C : Code n) (y : Word n) :
    tupleWord C (wordTuple C y) = y := by sorry
