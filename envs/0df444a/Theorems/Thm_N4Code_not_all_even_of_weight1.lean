-- Prove2me | Theorems.Thm_N4Code_not_all_even_of_weight1
-- name    : N4Code.not_all_even_of_weight1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:59:41.361934+00:00
-- url     : https://prove2.me/theorems/aebda026-075d-5753-9812-6ea44ba6519f
-- title:
--   N4 Code: not all even of weight1
-- statement:
--   A weight-1 column is odd, so the code is not all-even.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L408-L415
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L408-L415

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

theorem N4Code.not_all_even_of_weight1 {n : ℕ} (C : Code n) (h : ∃ t : Fin n, colWeight (C t) = 1) :
    ¬ allEvenWeights C := by sorry
