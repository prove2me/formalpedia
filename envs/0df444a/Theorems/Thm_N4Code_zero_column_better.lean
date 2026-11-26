-- Prove2me | Theorems.Thm_N4Code_zero_column_better
-- name    : N4Code.zero_column_better
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:10:43.395253+00:00
-- url     : https://prove2.me/theorems/79d56849-dc3a-4a16-aad1-140e663435de
-- title:
--   N4 Code: zero column better
-- statement:
--   Theorem `thm:0column` (Theorem 6) engine: replacing a 0-column never worsens λ, and
--   equality holds exactly when the set Y3c (eq. 6) is empty.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L514-L562
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/ZeroColumn.lean#L514-L562

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000

theorem N4Code.zero_column_better {n : ℕ} (C : Code n) (t : Fin n) (s' : Column)
    (hcol : C t = col0) (hO : (colZeros s').Nonempty) (hP : (colOnes s').Nonempty) :
    UniversalBetter (replaceColumn C t s') C ∧
      (UniversalEqual (replaceColumn C t s') C ↔ ∀ y : Word n, ¬ Y3c C s' hO hP t y) := by sorry
