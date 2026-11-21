-- Prove2me | Theorems.Thm_JardenShami_additive_isLocallyAdditive
-- name    : JardenShami.additive_isLocallyAdditive
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:40:44.837049+00:00
-- url     : https://prove2.me/theorems/d3ad15ac-5ec5-4650-8320-f5ed18e05bfb
-- title:
--   Jarden Shami: additive is Locally Additive
-- statement:
--   **Remark 2.7** (Section 2). Every additive coloring is locally-additive.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section2.lean#L136-L140
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section2.lean#L136-L140

import Mathlib.Data.Sym.Sym2
import Mathlib.SetTheory.Cardinal.Regular
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section2
set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
variable {A : Type w} [LinearOrder A] {D : Type v}

theorem JardenShami.additive_isLocallyAdditive {C : Coloring A D} (hC : IsAdditive C) :
    IsLocallyAdditive C := by sorry
