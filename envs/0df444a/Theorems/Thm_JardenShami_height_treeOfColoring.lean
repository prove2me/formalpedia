-- Prove2me | Theorems.Thm_JardenShami_height_treeOfColoring
-- name    : JardenShami.height_treeOfColoring
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:44:09.317161+00:00
-- url     : https://prove2.me/theorems/e81377ab-85fc-4ee6-88ff-6b76e825f732
-- title:
--   Jarden Shami: height tree Of Coloring
-- statement:
--   AUX: not in paper. The height of `T(C)` is `κ`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L298-L312
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L298-L312

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}} {D : Type w}

theorem JardenShami.height_treeOfColoring (C : Coloring (Kappa κ) D) :
    height (treeOfColoring C) = κ.ord := by sorry
