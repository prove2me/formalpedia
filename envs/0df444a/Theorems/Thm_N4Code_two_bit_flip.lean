-- Prove2me | Theorems.Thm_N4Code_two_bit_flip
-- name    : N4Code.two_bit_flip
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T10:29:55.066853+00:00
-- url     : https://prove2.me/theorems/3bd31f57-8902-4f8e-b789-897f99b32826
-- title:
--   N4 Code: two bit flip
-- statement:
--   Theorem `thm:odd` (Theorem 11) (2-bit flip): replacing type-1 and type-7 columns by
--   types 3 and 5 is never worse; equality iff |1|=|7|=1, |2|=|4|=|6|=0 and
--   |3| or |5| is odd.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L2835-L3360
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L2835-L3360

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.two_bit_flip {n : ℕ} (C C' : Code n) (t₁ t₂ : Fin n) (hne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (h3 : C' t₁ = col3) (h5 : C' t₂ = col5)
    (hsame : ∀ u : Fin n, u ≠ t₁ → u ≠ t₂ → C' u = C u)
    (h07 : Columns07 C) :
    UniversalBetter C' C ∧
      (UniversalEqual C' C ↔
        count C 1 = 1 ∧ count C 7 = 1 ∧ count C 2 = 0 ∧ count C 4 = 0 ∧
          count C 6 = 0 ∧ (Odd (count C 3) ∨ Odd (count C 5))) ∧
      (UniversalStrictBetter C' C ↔
        ¬ (count C 1 = 1 ∧ count C 7 = 1 ∧ count C 2 = 0 ∧ count C 4 = 0 ∧
          count C 6 = 0 ∧ (Odd (count C 3) ∨ Odd (count C 5)))) := by sorry
