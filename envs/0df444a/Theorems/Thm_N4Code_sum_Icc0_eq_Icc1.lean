-- Prove2me | Theorems.Thm_N4Code_sum_Icc0_eq_Icc1
-- name    : N4Code.sum_Icc0_eq_Icc1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:06:26.134334+00:00
-- url     : https://prove2.me/theorems/37f1a382-f28d-50e2-a5e2-ac25b0e7a420
-- title:
--   N4 Code: sum Icc0 eq Icc1
-- statement:
--   Dropping the d = 0 term of an interval sum when a(0) = 0.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L807-L832
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L807-L832

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
set_option autoImplicit true
open N4Code

theorem N4Code.sum_Icc0_eq_Icc1 {n : ℕ} (a : ℕ → ℝ) (ha : a 0 = 0) :
    (∑ d ∈ Finset.Icc 0 n, a d) = ∑ d ∈ Finset.Icc 1 n, a d := by sorry
