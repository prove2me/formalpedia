-- Prove2me | Theorems.Thm_N4Code_IsLinear_all_even
-- name    : N4Code.IsLinear_all_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:59:34.927441+00:00
-- url     : https://prove2.me/theorems/691f3c2d-4784-52c2-97b1-3266b8019265
-- title:
--   N4 Code: Is Linear all even
-- statement:
--   Linear codes have only even-weight columns.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L352-L374
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Performance.lean#L352-L374

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

theorem N4Code.IsLinear_all_even {n : ℕ} (C : Code n) (h : IsLinear C) : allEvenWeights C := by sorry
