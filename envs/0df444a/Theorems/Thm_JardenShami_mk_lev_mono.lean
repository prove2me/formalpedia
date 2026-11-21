-- Prove2me | Theorems.Thm_JardenShami_mk_lev_mono
-- name    : JardenShami.mk_lev_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:44:30.786769+00:00
-- url     : https://prove2.me/theorems/48012a34-0587-424f-b2ca-41b92aa32a22
-- title:
--   Jarden Shami: mk lev mono
-- statement:
--   AUX: not in paper. In a well-pruned tree, the sizes of the levels are non-decreasing (the
--   restriction map `Lev_β(T) → Lev_α(T)` is onto).
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L643-L656
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L643-L656

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7
set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree

theorem JardenShami.mk_lev_mono {T : Type w} [PartialOrder T] [IsTree T] (hwp : WellPruned T)
    {α β : Ordinal.{w}} (hαβ : α ≤ β) (hβ : β < height T) : #(Lev T α) ≤ #(Lev T β) := by sorry
