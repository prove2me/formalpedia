-- Prove2me | Theorems.Thm_N4Code_w_i_eq_card_onesOn
-- name    : N4Code.w_i_eq_card_onesOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:56:22.748799+00:00
-- url     : https://prove2.me/theorems/7f1ba2e7-410e-5323-80ff-e314e738ac82
-- title:
--   N4 Code: w i eq card ones On
-- statement:
--   The N4 Code construction uses the w i eq card ones On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L289-L290
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Basic.lean#L289-L290

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

theorem N4Code.w_i_eq_card_onesOn {n : ℕ} (C : Code n) (i : ℕ) (y : Word n) :
    w_i C i y = (onesOn (fiber C i) y).card := by sorry
