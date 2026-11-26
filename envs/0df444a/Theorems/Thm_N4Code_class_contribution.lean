-- Prove2me | Theorems.Thm_N4Code_class_contribution
-- name    : N4Code.class_contribution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:57:10.552938+00:00
-- url     : https://prove2.me/theorems/a57d9114-dc80-5c21-9905-82ddbedfb850
-- title:
--   N4 Code: class contribution
-- statement:
--   The columns of type i contribute `w_i` (bit j = 0) or `|i| − w_i`
--   (bit j = 1) to d_j(y) — paper eq. (d1)–(d4), §3.1.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L299-L358
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L299-L358

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

theorem N4Code.class_contribution {n : ℕ} (C : Code n) (j : Fin 4) (y : Word n) (i : ℕ) :
    (∑ t ∈ (Finset.univ.filter fun t : Fin n => colVal (C t) = i),
        if C t j ≠ y t then 1 else 0) =
      if i.testBit (3 - j.val) then count C i - w_i C i y else w_i C i y := by sorry
