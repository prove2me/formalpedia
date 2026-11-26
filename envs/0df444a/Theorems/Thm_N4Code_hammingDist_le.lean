-- Prove2me | Theorems.Thm_N4Code_hammingDist_le
-- name    : N4Code.hammingDist_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:57:05.580822+00:00
-- url     : https://prove2.me/theorems/59316f92-82d5-4fdf-8495-dcbc35a00f2a
-- title:
--   N4 Code: hamming Dist le
-- statement:
--   Hamming distance between two n-bit words is at most n.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L99-L107
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L99-L107

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

theorem N4Code.hammingDist_le {n : ℕ} (x y : Word n) : hammingDist x y ≤ n := by sorry
