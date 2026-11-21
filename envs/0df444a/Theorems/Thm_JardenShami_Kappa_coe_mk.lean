-- Prove2me | Theorems.Thm_JardenShami_Kappa_coe_mk
-- name    : JardenShami.Kappa.coe_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:41:33.869625+00:00
-- url     : https://prove2.me/theorems/a82c598e-4a28-4afd-b7c7-6bb5f220ff24
-- title:
--   Kappa: coe mk
-- statement:
--   AUX: not in paper.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L540-L542
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L540-L542

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

theorem JardenShami.Kappa.coe_mk (α : Ordinal.{w}) (h : α < κ.ord) :
    ((Kappa.mk α h : Kappa κ) : Ordinal.{w}) = α := by sorry
