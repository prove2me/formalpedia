-- Prove2me | Theorems.Thm_JardenShami_Kappa_coe_lt_coe
-- name    : JardenShami.Kappa.coe_lt_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:41:29.652673+00:00
-- url     : https://prove2.me/theorems/46e0ba0a-e2d8-4a7d-86ac-56a97dc5f611
-- title:
--   Kappa: coe lt coe
-- statement:
--   AUX: not in paper. Elements of `Kappa κ` as ordinals: `<` is preserved.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L525-L526
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L525-L526

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

theorem JardenShami.Kappa.coe_lt_coe {x y : Kappa κ} : (x : Ordinal.{w}) < y ↔ x < y := by sorry
