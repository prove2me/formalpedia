-- Prove2me | Theorems.Thm_N4Code_alpha_eq_card
-- name    : N4Code.alpha_eq_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:59:00.376718+00:00
-- url     : https://prove2.me/theorems/0ad35f33-d023-41c0-b9a0-2d2ad8c81f00
-- title:
--   N4 Code: alpha eq card
-- statement:
--   α_C(d) as the number of words at distance d (cardinality form).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L239-L241
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L239-L241

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

theorem N4Code.alpha_eq_card {n : ℕ} (C : Code n) (d : ℕ) :
    alpha C d = (Finset.univ.filter fun y : Word n => dCode C y = d).card := by sorry
