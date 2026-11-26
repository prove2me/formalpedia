-- Prove2me | Theorems.Thm_N4Code_compare_bij_eq
-- name    : N4Code.compare_bij_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:02:47.461639+00:00
-- url     : https://prove2.me/theorems/7640f9bc-5230-5fdb-a755-c168386ee33b
-- title:
--   N4 Code: compare bij eq
-- statement:
--   Lemma `thm:com` (Lemma 18), equality version: if the images are always equidistant
--   then the codes are equally good.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Comparison.lean#L92-L99
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Comparison.lean#L92-L99

import Definitions.Def_N4Code_Performance
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Comparison
set_option autoImplicit true
open N4Code

theorem N4Code.compare_bij_eq {n : ℕ} (C C' : Code n) (g : Word n ≃ Word n)
    (heq : ∀ y : Word n, dCode C y = dCode C' (g y)) :
    UniversalEqual C' C := by sorry
