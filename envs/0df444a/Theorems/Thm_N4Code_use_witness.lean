-- Prove2me | Theorems.Thm_N4Code_use_witness
-- name    : N4Code.use_witness
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:13:50.059835+00:00
-- url     : https://prove2.me/theorems/3d8ef788-c354-4783-9e2d-eb08f66a58f5
-- title:
--   N4 Code: use witness
-- statement:
--   Wrapper: the tableK bookkeeping for a feasible table assignment.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1565-L1590
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1565-L1590

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.use_witness {n : ℕ} (C : Code n) (h07 : Columns07 C) (hcnt0 : 1 ≤ count C 0)
    (a4 a5 a6 a7 : ℕ)
    (ha4 : a4 ≤ count C 4) (ha5 : a5 ≤ count C 5) (ha6 : a6 ≤ count C 6)
    (ha7 : a7 ≤ count C 7)
    (hmid : 2 * (a4 + a5 + a6 + a7) = count C 4 + count C 5 + count C 6 + count C 7)
    (hge2 : 2 * a6 + 2 * a7 ≤ count C 2 + count C 3 + count C 6 + count C 7)
    (hge3 : 2 * a5 + 2 * a7 ≤ count C 1 + count C 3 + count C 5 + count C 7) :
    ∃ t : Fin n, C t = col0 ∧ ∃ y : Word n, Y3c C col5 colZeros_col5_nonempty
      colOnes_col5_nonempty t y := by sorry
