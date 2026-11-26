-- Prove2me | Theorems.Thm_N4Code_g2_bijective
-- name    : N4Code.g2_bijective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:20:36.863347+00:00
-- url     : https://prove2.me/theorems/0fc7b017-b829-4878-9902-b405ba2c04fb
-- title:
--   N4 Code: g2 bijective
-- statement:
--   Lemma `lemma:2` (Lemma 22): g2 is a bijection.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L728-L748
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L728-L748

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.g2_bijective {n : ℕ} (C _C' : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) :
    Function.Bijective (g2 C t₁ t₂) := by sorry
