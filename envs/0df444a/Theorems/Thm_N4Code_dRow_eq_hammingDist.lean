-- Prove2me | Theorems.Thm_N4Code_dRow_eq_hammingDist
-- name    : N4Code.dRow_eq_hammingDist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:57:12.454201+00:00
-- url     : https://prove2.me/theorems/976756b4-ba33-4093-a5b8-00b20f2d55f4
-- title:
--   N4 Code: d Row eq hamming Dist
-- statement:
--   d_j(y) is the Hamming distance from y to the j-th codeword (paper eq. (d)).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L152-L153
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L152-L153

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

theorem N4Code.dRow_eq_hammingDist {n : ℕ} (C : Code n) (j : Fin 4) (y : Word n) :
    dRow C j y = hammingDist (row C j) y := by sorry
