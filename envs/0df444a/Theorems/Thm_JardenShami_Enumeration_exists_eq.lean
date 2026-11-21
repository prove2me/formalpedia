-- Prove2me | Theorems.Thm_JardenShami_Enumeration_exists_eq
-- name    : JardenShami.Enumeration.exists_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:42:47.174818+00:00
-- url     : https://prove2.me/theorems/7285f257-647b-4582-ad8b-c982a06ddc4d
-- title:
--   Enumeration: exists eq
-- statement:
--   AUX: not in paper. Every node of `Lev_α(T)` is some `t^i_α`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L779-L781
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L779-L781

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

theorem JardenShami.Enumeration.exists_eq (e : Enumeration κ T) {α : Ordinal.{w}} (hα : α < κ.ord) {x : T}
    (hx : x ∈ Lev T α) : ∃ i < (#(Lev T α)).ord, e.t α i = x := by sorry
