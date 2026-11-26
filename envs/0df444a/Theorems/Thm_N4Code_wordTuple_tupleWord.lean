-- Prove2me | Theorems.Thm_N4Code_wordTuple_tupleWord
-- name    : N4Code.wordTuple_tupleWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:57:31.562729+00:00
-- url     : https://prove2.me/theorems/b6a90fb4-b443-5635-bf7b-e69afd69b86a
-- title:
--   N4 Code: word Tuple tuple Word
-- statement:
--   Building a tuple from a tuple-built word recovers the tuple.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L479-L484
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L479-L484

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

theorem N4Code.wordTuple_tupleWord {n : ℕ} (C : Code n) (k : ℕ → ℕ)
    {g : Fin 16 → Finset (Fin n)} (hg : GoodTuplePred C k g) :
    wordTuple C (tupleWord C g) = g := by sorry
