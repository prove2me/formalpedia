-- Prove2me | Theorems.Thm_JardenShami_Kappa_card_eq_of_forall_exists_gt
-- name    : JardenShami.Kappa.card_eq_of_forall_exists_gt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:42:38.227111+00:00
-- url     : https://prove2.me/theorems/6897ec9e-6599-483f-b4c9-8c96dbfd54ac
-- title:
--   Kappa: card eq of forall exists gt
-- statement:
--   AUX: not in paper. For regular `κ`, an unbounded subset of `κ` has size `κ`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L99-L105
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L99-L105

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

theorem JardenShami.Kappa.card_eq_of_forall_exists_gt (hκ : κ.IsRegular) {S : Set (Kappa κ)}
    (h : ∀ x, ∃ y ∈ S, x < y) : #S = κ := by sorry
