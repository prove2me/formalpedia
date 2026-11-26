-- Prove2me | Theorems.Thm_N4Code_alpha3_zero
-- name    : N4Code.alpha3_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:06:37.144408+00:00
-- url     : https://prove2.me/theorems/4f0194a1-b317-48eb-8c10-f73fc4c23264
-- title:
--   N4 Code: alpha3 zero
-- statement:
--   α_C³(0) = 0: words in Y3 have distance at least one (paper `the:1` (Theorem 20)).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L746-L754
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L746-L754

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
set_option autoImplicit true
open N4Code

theorem N4Code.alpha3_zero {n : ℕ} (C C' : Code n) (t : Fin n) (hcol : C t = col1)
    (hcol' : C' t = col3) (hsame : ∀ u : Fin n, u ≠ t → C' u = C u) :
    alpha3 C t 0 = 0 := by sorry
