-- Prove2me | Theorems.Thm_N4Code_z_partition
-- name    : N4Code.z_partition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:19:37.72355+00:00
-- url     : https://prove2.me/theorems/1aa4e5c7-7a6e-5dce-a1e9-4141147fdccd
-- title:
--   N4 Code: z partition
-- statement:
--   Lemma `lemma:2` (Lemma 22): Z1..Z5 form a partition of the word space.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L439-L519
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L439-L519

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.z_partition {n : ℕ} (C _C' : Code n) (t₁ t₂ : Fin n) :
    ∀ y : Word n, ∃! i : Fin 5, ZSet C t₁ t₂ i y := by sorry
