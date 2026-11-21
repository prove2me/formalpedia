-- Prove2me | Theorems.Thm_JardenShami_mk_levLt_lt
-- name    : JardenShami.mk_levLt_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:44:28.272496+00:00
-- url     : https://prove2.me/theorems/ce600bc1-9622-4851-87b7-9f81a88f6de6
-- title:
--   Jarden Shami: mk lev Lt lt
-- statement:
--   AUX: not in paper. In a `κ`-tree (`κ` regular), the nodes of height `< α` (`α < κ`) are
--   fewer than `κ`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L364-L380
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L364-L380

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7
set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree
variable {T : Type w} [PartialOrder T] [IsTree T]

theorem JardenShami.mk_levLt_lt {κ : Cardinal.{w}} (hκ : κ.IsRegular) (hT : IsKappaTree κ T)
    {α : Ordinal.{w}} (hα : α < κ.ord) : #{s : T | ht s < α} < κ := by sorry
