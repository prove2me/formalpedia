-- Prove2me | Theorems.Thm_N4Code_dRow_eq_sum
-- name    : N4Code.dRow_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:01:08.466624+00:00
-- url     : https://prove2.me/theorems/f2a88711-2ad4-581f-8448-1b3df8b90d2f
-- title:
--   N4 Code: d Row eq sum
-- statement:
--   d_j(y) expressed through the per-type weights w_i (paper eq. d1–d4).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L361-L386
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L361-L386

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

theorem N4Code.dRow_eq_sum {n : ℕ} (C : Code n) (j : Fin 4) (y : Word n) :
    dRow C j y = ∑ i ∈ Finset.Icc 0 15,
      if i.testBit (3 - j.val) then count C i - w_i C i y else w_i C i y := by sorry
