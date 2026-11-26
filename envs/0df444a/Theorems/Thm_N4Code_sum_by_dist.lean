-- Prove2me | Theorems.Thm_N4Code_sum_by_dist
-- name    : N4Code.sum_by_dist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:05:15.300999+00:00
-- url     : https://prove2.me/theorems/47c5a15c-0568-5cac-9f66-9305a6e54411
-- title:
--   N4 Code: sum by dist
-- statement:
--   Group a sum over filtered words by their distance to C.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L773-L804
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L773-L804

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
set_option autoImplicit true
open N4Code

theorem N4Code.sum_by_dist {n : ℕ} (C : Code n) (P : Word n → Prop) [DecidablePred P]
    (f : ℕ → ℝ) :
    (∑ y ∈ (Finset.univ.filter P), f (dCode C y)) =
      ∑ d ∈ Finset.Icc 0 n,
        ((Finset.univ.filter fun y : Word n => P y ∧ dCode C y = d).card : ℝ) * f d := by sorry
