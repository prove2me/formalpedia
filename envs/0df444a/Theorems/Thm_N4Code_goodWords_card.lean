-- Prove2me | Theorems.Thm_N4Code_goodWords_card
-- name    : N4Code.goodWords_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:57:58.236056+00:00
-- url     : https://prove2.me/theorems/6910240f-7550-4adb-9802-8008471666ce
-- title:
--   N4 Code: good Words card
-- statement:
--   Good words and good tuples are equinumerous.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L487-L514
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L487-L514

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

theorem N4Code.goodWords_card {n : ℕ} (C : Code n) (k : ℕ → ℕ) :
    (GoodWords C k).card = (GoodTuples C k).card := by sorry
