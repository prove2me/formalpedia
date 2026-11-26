-- Prove2me | Theorems.Thm_N4Code_dCode_replace_flip_27
-- name    : N4Code.dCode_replace_flip_27
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:19:22.602827+00:00
-- url     : https://prove2.me/theorems/68992652-a31e-52c9-8e1f-c3eb2fe0babb
-- title:
--   N4 Code: d Code replace flip 27
-- statement:
--   d_{C'}(F₂ y) = min(d_O'(y), d_P(y)) for the two-column change (paper eq. dcpf).
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L373-L379
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L373-L379

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.dCode_replace_flip_27 {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂) (y : Word n)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) :
    dCode (replaceColumn (replaceColumn C t₁ col3) t₂ col5) (flipTwoBits t₁ t₂ y) =
      min (dOp2 C t₁ t₂ y) (dP C y) := by sorry
