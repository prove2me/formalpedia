-- Prove2me | Theorems.Thm_JardenShami_Kappa_coe_inj
-- name    : JardenShami.Kappa.coe_inj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:41:33.227671+00:00
-- url     : https://prove2.me/theorems/ea361783-849c-4385-beb9-4ec4b1e4c89c
-- title:
--   Kappa: coe inj
-- statement:
--   AUX: not in paper.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L545-L546
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L545-L546

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

theorem JardenShami.Kappa.coe_inj {x y : Kappa κ} : (x : Ordinal.{w}) = y ↔ x = y := by sorry
