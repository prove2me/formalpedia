-- Prove2me | Theorems.Thm_N4Code_hammingDist_self
-- name    : N4Code.hammingDist_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:57:50.100818+00:00
-- url     : https://prove2.me/theorems/1be976bf-0724-5b99-8ee1-324ed2668d6c
-- title:
--   N4 Code: hamming Dist self
-- statement:
--   Hamming distance is reflexive.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L78-L80
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L78-L80

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

theorem N4Code.hammingDist_self {n : ℕ} (x : Word n) : hammingDist x x = 0 := by sorry
