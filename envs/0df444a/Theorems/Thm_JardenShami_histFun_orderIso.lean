-- Prove2me | Theorems.Thm_JardenShami_histFun_orderIso
-- name    : JardenShami.histFun_orderIso
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:43:34.196034+00:00
-- url     : https://prove2.me/theorems/aa70b458-0d92-45f1-b1a5-855eb1c3b22f
-- title:
--   Jarden Shami: hist Fun order Iso
-- statement:
--   AUX: not in paper. Order isomorphisms of trees induce isomorphisms of history trees.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L406-L417
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L406-L417

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open Tree
variable {T : Type w} [PartialOrder T] [IsTree T]

theorem JardenShami.histFun_orderIso {S : Type w} [PartialOrder S] [IsTree S] (e : T ≃o S) (t : T) :
    histFun (e t) = Prod.map id e '' histFun t := by sorry
