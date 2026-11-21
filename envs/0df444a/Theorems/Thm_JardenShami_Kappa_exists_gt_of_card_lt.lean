-- Prove2me | Theorems.Thm_JardenShami_Kappa_exists_gt_of_card_lt
-- name    : JardenShami.Kappa.exists_gt_of_card_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:41:55.139739+00:00
-- url     : https://prove2.me/theorems/9c6e91bb-490a-477e-bddd-9027889844b8
-- title:
--   Kappa: exists gt of card lt
-- statement:
--   AUX: not in paper. For regular `κ`, a subset of `κ` of size `< κ` is bounded.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L88-L96
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L88-L96

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}}

theorem JardenShami.Kappa.exists_gt_of_card_lt (hκ : κ.IsRegular) {S : Set (Kappa κ)} (hS : #S < κ) :
    ∃ x, ∀ y ∈ S, y < x := by sorry
