-- Prove2me | Theorems.Thm_N4Code_twobitCount_equiv
-- name    : N4Code.twobitCount_equiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:16:02.905861+00:00
-- url     : https://prove2.me/theorems/c4aee2cb-58ee-4b77-a527-1c3aa005b878
-- title:
--   N4 Code: twobit Count equiv
-- statement:
--   The number of two-bit columns is invariant under equivalence.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2652-L2681
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L2652-L2681

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.twobitCount_equiv {n : ℕ} {C C' : Code n} (h : Equivalent C C') :
    twobitCount C = twobitCount C' := by sorry
