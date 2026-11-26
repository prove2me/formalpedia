-- Prove2me | Theorems.Thm_N4Code_onesOn_tupleWord
-- name    : N4Code.onesOn_tupleWord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:56:39.930968+00:00
-- url     : https://prove2.me/theorems/cf375a2e-ad7a-41e5-9561-9e167da2b286
-- title:
--   N4 Code: ones On tuple Word
-- statement:
--   The ones of `tupleWord C g` on the type-i columns equal the tuple's set.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L428-L448
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L428-L448

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

theorem N4Code.onesOn_tupleWord {n : ℕ} (C : Code n) (k : ℕ → ℕ) (g : Fin 16 → Finset (Fin n))
    (hg : GoodTuplePred C k g) {i : ℕ} (hi : i ∈ Finset.Icc 0 15) :
    onesOn (fiber C i) (tupleWord C g) = g ⟨i, by
      have hi' : i ≤ 15 := (Finset.mem_Icc.mp hi).2
      omega⟩ := by sorry
