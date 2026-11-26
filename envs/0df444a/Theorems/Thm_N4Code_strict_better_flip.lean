-- Prove2me | Theorems.Thm_N4Code_strict_better_flip
-- name    : N4Code.strict_better_flip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:15:55.423003+00:00
-- url     : https://prove2.me/theorems/e9499548-1e09-53b0-a3e4-661852867be5
-- title:
--   N4 Code: strict better flip
-- statement:
--   Flipping the changed column preserves strict improvement (equivalence).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2475-L2489
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2475-L2489

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.strict_better_flip {n : ℕ} (C : Code n) (t : Fin n) (s : Column)
    (h : UniversalStrictBetter (replaceColumn C t s) C) :
    UniversalStrictBetter (replaceColumn C t (flipCol s)) C := by sorry
