-- Prove2me | Theorems.Thm_N4Code_tupleWord_mem
-- name    : N4Code.tupleWord_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:57:29.418667+00:00
-- url     : https://prove2.me/theorems/82a92464-eac1-5e07-b6b9-a7c1108fbfb7
-- title:
--   N4 Code: tuple Word mem
-- statement:
--   A good tuple maps to a good word.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L462-L470
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L462-L470

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

theorem N4Code.tupleWord_mem {n : ℕ} (C : Code n) (k : ℕ → ℕ) {g : Fin 16 → Finset (Fin n)}
    (hg : GoodTuplePred C k g) : tupleWord C g ∈ GoodWords C k := by sorry
