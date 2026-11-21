-- Prove2me | Theorems.Thm_JardenShami_zero_lt_ord_lev
-- name    : JardenShami.zero_lt_ord_lev
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:41:40.850963+00:00
-- url     : https://prove2.me/theorems/6eb93d4c-24eb-49d6-a1e5-5fb0378681e3
-- title:
--   Jarden Shami: zero lt ord lev
-- statement:
--   AUX: not in paper. In a `κ`-tree, `0 < μ_α` for `α < κ`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L773-L776
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L773-L776

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

theorem JardenShami.zero_lt_ord_lev (hT : IsKappaTree κ T) {α : Ordinal.{w}} (hα : α < κ.ord) :
    0 < (#(Lev T α)).ord := by sorry
