-- Prove2me | Theorems.Thm_JardenShami_colorMaxOf_color
-- name    : JardenShami.colorMaxOf_color
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:43:43.042586+00:00
-- url     : https://prove2.me/theorems/2276ad65-20fd-4dff-95af-a3d3e14cf3e6
-- title:
--   Jarden Shami: color Max Of color
-- statement:
--   AUX: not in paper. `C_f(a,b) = f(b)` for `a < b`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L696-L699
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L696-L699

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}} {D : Type v}

theorem JardenShami.colorMaxOf_color (f : Kappa κ → Fin 2) (a b : Kappa κ) (h : a < b) :
    (colorMaxOf f).color a b h = f b := by sorry
