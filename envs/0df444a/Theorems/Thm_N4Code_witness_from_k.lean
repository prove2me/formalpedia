-- Prove2me | Theorems.Thm_N4Code_witness_from_k
-- name    : N4Code.witness_from_k
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:10:58.160348+00:00
-- url     : https://prove2.me/theorems/ead16367-ba42-4f8e-a49e-6b49a16e04f4
-- title:
--   N4 Code: witness from k
-- statement:
--   From a feasible table assignment k, build the witness word and prove
--   Y3c nonempty for the col5 split (paper Table 0column).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1216-L1342
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L1216-L1342

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.witness_from_k {n : ℕ} (C : Code n) (h07 : Columns07 C) (k : ℕ → ℕ)
    (hcnt0 : 1 ≤ count C 0) (hk0 : k 0 = 1)
    (hk03 : k 1 = 0 ∧ k 2 = 0 ∧ k 3 = 0)
    (hk47 : ∀ i ∈ Finset.Icc 4 7, k i ≤ count C i)
    (hk815 : ∀ i ∈ Finset.Icc 8 15, k i = 0)
    (hmid : 2 * (k 4 + k 5 + k 6 + k 7) =
      count C 4 + count C 5 + count C 6 + count C 7)
    (hge2 : 2 * k 6 + 2 * k 7 ≤ count C 2 + count C 3 + count C 6 + count C 7)
    (hge3 : 2 * k 5 + 2 * k 7 ≤ count C 1 + count C 3 + count C 5 + count C 7) :
    ∃ t : Fin n, C t = col0 ∧ ∃ y : Word n, Y3c C col5 colZeros_col5_nonempty
      colOnes_col5_nonempty t y := by sorry
