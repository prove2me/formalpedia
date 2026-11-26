-- Prove2me | Theorems.Thm_N4Code_compare_bij_strict
-- name    : N4Code.compare_bij_strict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:02:44.511314+00:00
-- url     : https://prove2.me/theorems/c2f31f38-e371-5f61-b797-9aedece11ffa
-- title:
--   N4 Code: compare bij strict
-- statement:
--   Lemma `thm:com` (Lemma 18), strict version: if S is nonempty then C' is strictly
--   better than C.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Comparison.lean#L72-L88
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Comparison.lean#L72-L88

import Definitions.Def_N4Code_Performance
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Comparison
set_option autoImplicit true
open N4Code

theorem N4Code.compare_bij_strict {n : ℕ} (C C' : Code n) (S : Finset (Word n))
    (g : Word n ≃ Word n)
    (hgt : ∀ y : Word n, y ∈ S → dCode C y > dCode C' (g y))
    (heq : ∀ y : Word n, y ∉ S → dCode C y = dCode C' (g y))
    (hne : ∃ y : Word n, y ∈ S) : UniversalStrictBetter C' C := by sorry
