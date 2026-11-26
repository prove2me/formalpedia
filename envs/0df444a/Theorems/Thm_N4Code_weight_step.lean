-- Prove2me | Theorems.Thm_N4Code_weight_step
-- name    : N4Code.weight_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:58:57.992853+00:00
-- url     : https://prove2.me/theorems/3be721cd-e897-4c1e-a75f-2cc8feab148e
-- title:
--   N4 Code: weight step
-- statement:
--   Moving one step further from the code strictly decreases the weight.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L28-L60
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L28-L60

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

theorem N4Code.weight_step {n : ℕ} {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2) (x : ℕ) :
    weight n ε (x + 1) < weight n ε x := by sorry
