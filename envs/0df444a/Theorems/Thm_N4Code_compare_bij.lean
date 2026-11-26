-- Prove2me | Theorems.Thm_N4Code_compare_bij
-- name    : N4Code.compare_bij
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:02:46.409878+00:00
-- url     : https://prove2.me/theorems/8197659d-019c-4bbe-ad98-bd3943a8c4bb
-- title:
--   N4 Code: compare bij
-- statement:
--   Lemma `thm:com` (Lemma 18): a bijection with strictly closer images on S and equality
--   off S makes C' at least as good as C.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Comparison.lean#L55-L68
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Comparison.lean#L55-L68

import Definitions.Def_N4Code_Performance
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Comparison
set_option autoImplicit true
open N4Code

theorem N4Code.compare_bij {n : ℕ} (C C' : Code n) (S : Finset (Word n))
    (g : Word n ≃ Word n)
    (hgt : ∀ y : Word n, y ∈ S → dCode C y > dCode C' (g y))
    (heq : ∀ y : Word n, y ∉ S → dCode C y = dCode C' (g y)) :
    UniversalBetter C' C := by sorry
