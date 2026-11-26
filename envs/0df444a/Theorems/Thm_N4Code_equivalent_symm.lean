-- Prove2me | Theorems.Thm_N4Code_equivalent_symm
-- name    : N4Code.equivalent_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:25:11.663483+00:00
-- url     : https://prove2.me/theorems/8835d2f9-b9c6-5f23-80c6-7993d3ca77d8
-- title:
--   N4 Code: equivalent symm
-- statement:
--   Equivalence is symmetric.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2313-L2347
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2313-L2347

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.equivalent_symm {n : ℕ} {C C' : Code n} (h : Equivalent C C') : Equivalent C' C := by sorry
