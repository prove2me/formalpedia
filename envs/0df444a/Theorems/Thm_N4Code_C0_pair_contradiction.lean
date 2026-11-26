-- Prove2me | Theorems.Thm_N4Code_C0_pair_contradiction
-- name    : N4Code.C0_pair_contradiction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:13:13.100812+00:00
-- url     : https://prove2.me/theorems/72e241bf-ce02-4048-bbae-26d19754137a
-- title:
--   N4 Code: C0 pair contradiction
-- statement:
--   For the C0 code with |5| and |6| odd, no two rows share a distance value
--   that is no larger than the other two (paper `thm:0column` (Theorem 6) proof).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L687-L771
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L687-L771

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.C0_pair_contradiction {n : ℕ} (C : Code n)
    (hC : ∀ u : Fin n, colVal (C u) = 0 ∨ colVal (C u) = 5 ∨ colVal (C u) = 6)
    (h5 : Odd (count C 5)) (h6 : Odd (count C 6)) (y : Word n) :
    (dRow C 0 y ≠ dRow C 2 y) ∧
    (dRow C 0 y ≠ dRow C 3 y) ∧
    (dRow C 1 y ≠ dRow C 2 y) ∧
    (dRow C 1 y ≠ dRow C 3 y) ∧
    (¬ (dRow C 0 y = dRow C 1 y ∧ dRow C 0 y ≤ dRow C 2 y ∧ dRow C 0 y ≤ dRow C 3 y)) ∧
    (¬ (dRow C 2 y = dRow C 3 y ∧ dRow C 2 y ≤ dRow C 0 y ∧ dRow C 2 y ≤ dRow C 1 y)) := by sorry
