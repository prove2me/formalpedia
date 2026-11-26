-- Prove2me | Theorems.Thm_N4Code_even_two_mul
-- name    : N4Code.even_two_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:22:32.968957+00:00
-- url     : https://prove2.me/theorems/4f3b6bfd-2f24-4f94-b40c-06eddda71224
-- title:
--   N4 Code: even two mul
-- statement:
--   Even n gives a linear witness n = 2k.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1433-L1435
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1433-L1435

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.even_two_mul {n : ℕ} (h : Even n) : ∃ k : ℕ, n = 2 * k := by sorry
