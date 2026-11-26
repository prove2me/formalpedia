-- Prove2me | Theorems.Thm_N4Code_z5_nonempty_of_table
-- name    : N4Code.z5_nonempty_of_table
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:18:10.40417+00:00
-- url     : https://prove2.me/theorems/92dbe03e-45c1-4689-97b4-7eabcc7f83a7
-- title:
--   N4 Code: z5 nonempty of table
-- statement:
--   The N4 Code construction uses the z5 nonempty of table property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1763-L1819
-- source:
--   https://github.com/shhyang/n4code_lean/blob/1a501146e430d46c355aa937689f88f24e5ea822/N4Code/TwoColumn.lean#L1763-L1819

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators

theorem N4Code.z5_nonempty_of_table {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (htne : t₁ ≠ t₂)
    (h1 : C t₁ = col1) (h7 : C t₂ = col7) (h07 : Columns07 C)
    (a1 a2 a3 a4 a5 a6 a7 : ℕ) (c : ℕ) (hc : c ≤ 1)
    (ha1 : 1 ≤ a1) (ha7 : a7 + 1 ≤ count C 7)
    (hb1 : a1 ≤ count C 1) (hb2 : a2 ≤ count C 2) (hb3 : a3 ≤ count C 3)
    (hb4 : a4 ≤ count C 4) (hb5 : a5 ≤ count C 5) (hb6 : a6 ≤ count C 6)
    (hb7 : a7 ≤ count C 7)
    (h1eq : 2 * (a2 + a3) + count C 4 + count C 5 + c =
        2 * (a4 + a5) + count C 2 + count C 3)
    (h2ge : count C 2 + count C 3 + count C 6 + count C 7 - 1 ≤ 2 * (a2 + a3 + a6 + a7))
    (h3le : 2 * (a1 + a5) + count C 2 + count C 6 ≤
        2 * (a2 + a6) + count C 1 + count C 5 + 1) :
    ∃ y : Word n, Z5 C t₁ t₂ y := by sorry
