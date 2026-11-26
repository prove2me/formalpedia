-- Prove2me | Theorems.Thm_N4Code_cumulative_no_y5
-- name    : N4Code.cumulative_no_y5
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:07:37.724749+00:00
-- url     : https://prove2.me/theorems/13c52a94-c55f-48e4-878b-fb5c39562b2f
-- title:
--   N4 Code: cumulative no y5
-- statement:
--   Corollary `cor:1` (Corollary 21) (3): Y5 = ∅ ⇒ λ_{C'} ≥ λ_C, equality iff Y3 = ∅.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L1077-L1134
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L1077-L1134

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
set_option autoImplicit true
open N4Code

theorem N4Code.cumulative_no_y5 {n : ℕ} (C C' : Code n) (t : Fin n)
    (hcol : C t = col1) (hcol' : C' t = col3)
    (hsame : ∀ u : Fin n, u ≠ t → C' u = C u)
    (h5 : ∀ y : Word n, ¬ Y5 C t y) :
    UniversalBetter C' C ∧
      (UniversalEqual C' C ↔ ∀ y : Word n, ¬ Y3 C t y) := by sorry
