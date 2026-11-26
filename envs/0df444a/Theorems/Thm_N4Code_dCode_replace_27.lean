-- Prove2me | Theorems.Thm_N4Code_dCode_replace_27
-- name    : N4Code.dCode_replace_27
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:17:51.508267+00:00
-- url     : https://prove2.me/theorems/0b0c57d9-0430-47a0-b637-af92f06455ad
-- title:
--   N4 Code: d Code replace 27
-- statement:
--   d_{C'}(y) = min(d_O(y), d_P'(y)) for the two-column change (paper eq. dcp).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L355-L370
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L355-L370

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.dCode_replace_27 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂) (y : Word n)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) :
    dCode (replaceColumn (replaceColumn C t₁ col3) t₂ col5) y =
      min (dO C y) (dPp2 C t₁ t₂ y) := by sorry
