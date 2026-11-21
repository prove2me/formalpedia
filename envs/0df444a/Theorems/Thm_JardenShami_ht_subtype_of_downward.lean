-- Prove2me | Theorems.Thm_JardenShami_ht_subtype_of_downward
-- name    : JardenShami.ht_subtype_of_downward
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:43:19.079887+00:00
-- url     : https://prove2.me/theorems/3416b5b1-c8ba-461d-83b3-94bc887b1981
-- title:
--   Jarden Shami: ht subtype of downward
-- statement:
--   AUX: not in paper. In a downward closed subset `S` of a tree, heights computed in `S` and
--   in `T` agree.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L330-L339
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L330-L339

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7
set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree
variable {T : Type w} [PartialOrder T] [IsTree T]

theorem JardenShami.ht_subtype_of_downward {S : Set T} (hS : ∀ s ∈ S, ∀ t < s, t ∈ S) (x : S) :
    ht x = ht (x : T) := by sorry
