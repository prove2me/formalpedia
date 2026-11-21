-- Prove2me | Theorems.Thm_JardenShami_exists_mk_lev_const
-- name    : JardenShami.exists_mk_lev_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:44:32.895355+00:00
-- url     : https://prove2.me/theorems/9fd912b3-faaf-462a-8220-8f45157cd0a5
-- title:
--   Jarden Shami: exists mk lev const
-- statement:
--   AUX: not in paper. In a well-pruned `κ`-tree (`κ` regular) whose levels have size `< λ`,
--   `λ < κ`, the sizes of the levels are eventually constant.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L660-L704
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L660-L704

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7
set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree

theorem JardenShami.exists_mk_lev_const {κ lam : Cardinal.{w}} (hκ : κ.IsRegular) (hlam : lam < κ)
    {T : Type w} [PartialOrder T] [IsTree T] (hT : IsKappaTree κ T) (hwp : WellPruned T)
    (hlev : ∀ α : Ordinal.{w}, #(Lev T α) < lam) :
    ∃ α₀ < κ.ord, ∀ β : Ordinal.{w}, α₀ ≤ β → β < κ.ord → #(Lev T β) = #(Lev T α₀) := by sorry
