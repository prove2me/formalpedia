-- Prove2me | Theorems.Thm_N4Code_alpha5_n_zero
-- name    : N4Code.alpha5_n_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:06:13.039284+00:00
-- url     : https://prove2.me/theorems/9a8bfd64-5c23-5ffe-a8c6-fba7414111ce
-- title:
--   N4 Code: alpha5 n zero
-- statement:
--   α_C⁵(n) = 0: words in Y5 have distance at most n − 1 (paper `the:1` (Theorem 20)).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L757-L766
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Compare.lean#L757-L766

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
set_option autoImplicit true
open N4Code

theorem N4Code.alpha5_n_zero {n : ℕ} (C C' : Code n) (t : Fin n) (hcol : C t = col1)
    (hcol' : C' t = col3) (hsame : ∀ u : Fin n, u ≠ t → C' u = C u) :
    alpha5 C t n = 0 := by sorry
