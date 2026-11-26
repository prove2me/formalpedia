-- Prove2me | Theorems.Thm_N4Code_dCode_le_dRow
-- name    : N4Code.dCode_le_dRow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:57:06.757854+00:00
-- url     : https://prove2.me/theorems/564364ff-498b-4b5a-9b6a-539f4d60dde4
-- title:
--   N4 Code: d Code le d Row
-- statement:
--   d_C(y) is the minimum of the row distances.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L156-L163
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L156-L163

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

theorem N4Code.dCode_le_dRow {n : ℕ} (C : Code n) (j : Fin 4) (y : Word n) :
    dCode C y ≤ dRow C j y := by sorry
