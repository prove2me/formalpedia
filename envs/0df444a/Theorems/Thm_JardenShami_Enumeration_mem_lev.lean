-- Prove2me | Theorems.Thm_JardenShami_Enumeration_mem_lev
-- name    : JardenShami.Enumeration.mem_lev
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:43:47.793329+00:00
-- url     : https://prove2.me/theorems/fd8cfeba-da59-4daa-985f-326e1c8b9655
-- title:
--   Enumeration: mem lev
-- statement:
--   AUX: not in paper. `t^i_α ∈ Lev_α(T)`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L763-L765
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L763-L765

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

theorem JardenShami.Enumeration.mem_lev (e : Enumeration κ T) {α i : Ordinal.{w}} (hα : α < κ.ord)
    (hi : i < (#(Lev T α)).ord) : e.t α i ∈ Lev T α := by sorry
