-- Prove2me | Theorems.Thm_N4Code_y3c_empty_C0
-- name    : N4Code.y3c_empty_C0
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:13:09.083474+00:00
-- url     : https://prove2.me/theorems/bf3a96eb-6859-4d00-be51-dcf34c293596
-- title:
--   N4 Code: y3c empty C0
-- statement:
--   The C0 code has no words in Y3c, for any split (paper `thm:0column` (Theorem 6) (1)).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L774-L872
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L774-L872

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.y3c_empty_C0 {n : ℕ} (C : Code n) (t : Fin n) (s' : Column)
    (hO : (colZeros s').Nonempty) (hP : (colOnes s').Nonempty)
    (hC : ∀ u : Fin n, colVal (C u) = 0 ∨ colVal (C u) = 5 ∨ colVal (C u) = 6)
    (h5 : Odd (count C 5)) (h6 : Odd (count C 6)) :
    ∀ y : Word n, ¬ Y3c C s' hO hP t y := by sorry
