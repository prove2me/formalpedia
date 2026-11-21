-- Prove2me | Theorems.Thm_JardenShami_uMap_color
-- name    : JardenShami.uMap_color
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:40:47.046439+00:00
-- url     : https://prove2.me/theorems/0402d221-3a9c-405b-84ee-925a5f37cdda
-- title:
--   Jarden Shami: u Map color
-- statement:
--   **Notation 2.5** (Section 2), the defining equation `u_{a,b}(C(b,c)) = C(a,c)`, for a locally
--   additive `C` and `a < b < c`. (With the choice-based encoding of `uMap` this is a statement.)
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section2.lean#L103-L114
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section2.lean#L103-L114

import Mathlib.Data.Sym.Sym2
import Mathlib.SetTheory.Cardinal.Regular
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section2
set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
variable {A : Type w} [LinearOrder A] {D : Type v}

theorem JardenShami.uMap_color {C : Coloring A D} (hC : IsLocallyAdditive C) {a b c : A}
    (hab : a < b) (hbc : b < c) :
    uMap C a b hab ⟨C.color b c hbc, c, hbc, rfl⟩ = C.color a c (hab.trans hbc) := by sorry
