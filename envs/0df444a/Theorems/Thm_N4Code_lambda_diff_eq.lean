-- Prove2me | Theorems.Thm_N4Code_lambda_diff_eq
-- name    : N4Code.lambda_diff_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:59:37.628785+00:00
-- url     : https://prove2.me/theorems/6396e0f5-844e-429a-84db-622068b49afe
-- title:
--   N4 Code: lambda diff eq
-- statement:
--   The exact λ-difference behind `thm:com` (Lemma 18).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Comparison.lean#L19-L51
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/Comparison.lean#L19-L51

import Definitions.Def_N4Code_Performance
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Comparison
set_option autoImplicit true
open N4Code

theorem N4Code.lambda_diff_eq {n : ℕ} (C C' : Code n) (S : Finset (Word n))
    (g : Word n ≃ Word n)
    (_hgt : ∀ y : Word n, y ∈ S → dCode C y > dCode C' (g y))
    (heq : ∀ y : Word n, y ∉ S → dCode C y = dCode C' (g y)) (ε : ℝ) :
    lambda C' ε - lambda C ε =
      (1 / 4 : ℝ) * ∑ y ∈ S, (weight n ε (dCode C' (g y)) - weight n ε (dCode C y)) := by sorry
