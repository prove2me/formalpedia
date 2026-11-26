-- Prove2me | Theorems.Thm_N4Code_hammingDist_symm
-- name    : N4Code.hammingDist_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:58:13.560212+00:00
-- url     : https://prove2.me/theorems/77b17550-d279-467a-b117-53021364dbc5
-- title:
--   N4 Code: hamming Dist symm
-- statement:
--   Hamming distance is symmetric.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L83-L84
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L83-L84

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

theorem N4Code.hammingDist_symm {n : ℕ} (x y : Word n) : hammingDist x y = hammingDist y x := by sorry
