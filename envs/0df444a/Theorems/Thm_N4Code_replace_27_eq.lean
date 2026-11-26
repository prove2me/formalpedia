-- Prove2me | Theorems.Thm_N4Code_replace_27_eq
-- name    : N4Code.replace_27_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:17:29.331638+00:00
-- url     : https://prove2.me/theorems/91dea0c2-a2c0-511c-8ac3-bef2fae6a715
-- title:
--   N4 Code: replace 27 eq
-- statement:
--   C' is exactly the two-column replacement.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L382-L396
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L382-L396

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.replace_27_eq {n : ℕ} (C C' : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h3 : C' t₁ = col3) (h5 : C' t₂ = col5)
    (hsame : ∀ u : Fin n, u ≠ t₁ → u ≠ t₂ → C' u = C u) :
    C' = replaceColumn (replaceColumn C t₁ col3) t₂ col5 := by sorry
