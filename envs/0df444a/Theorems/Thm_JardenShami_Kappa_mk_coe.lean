-- Prove2me | Theorems.Thm_JardenShami_Kappa_mk_coe
-- name    : JardenShami.Kappa.mk_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:41:29.381439+00:00
-- url     : https://prove2.me/theorems/231389be-0999-455c-a4b6-f7e86b4ba335
-- title:
--   Kappa: mk coe
-- statement:
--   AUX: not in paper.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L881-L883
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L881-L883

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}} {T : Type w} [PartialOrder T] [IsTree T]

theorem JardenShami.Kappa.mk_coe {κ : Cardinal.{w}} (x : Kappa κ) :
    Kappa.mk (x : Ordinal.{w}) (Kappa.coe_lt_ord x) = x := by sorry
