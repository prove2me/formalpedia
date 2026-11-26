-- Prove2me | Theorems.Thm_N4Code_weight_strictAnti
-- name    : N4Code.weight_strictAnti
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:58:59.202048+00:00
-- url     : https://prove2.me/theorems/f6c0ca89-4959-430f-935e-363742af304c
-- title:
--   N4 Code: weight strict Anti
-- statement:
--   The weight is strictly decreasing in the distance (paper proof of `thm:com` (Lemma 18)).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L63-L77
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L63-L77

import Definitions.Def_N4Code_Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_Performance
set_option autoImplicit true
open scoped BigOperators
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.weight_strictAnti {n : ℕ} {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    ∀ {a b : ℕ}, a < b → weight n ε b < weight n ε a := by sorry
