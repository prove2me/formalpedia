-- Prove2me | Theorems.Thm_N4Code_dRow_replace_27_2
-- name    : N4Code.dRow_replace_27_2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:18:33.014637+00:00
-- url     : https://prove2.me/theorems/54814eef-eb7f-4a2a-9555-cab2ea8d2226
-- title:
--   N4 Code: d Row replace 27 2
-- statement:
--   Row 2 of the new code equals the old row-2 distance at the flipped word.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L333-L352
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L333-L352

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.dRow_replace_27_2 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (y : Word n) (h1 : C t₁ = col1) (h7 : C t₂ = col7) :
    dRow (replaceColumn (replaceColumn C t₁ col3) t₂ col5) ⟨2, by decide⟩ y =
      dRow C ⟨2, by decide⟩ (flipTwoBits t₁ t₂ y) := by sorry
