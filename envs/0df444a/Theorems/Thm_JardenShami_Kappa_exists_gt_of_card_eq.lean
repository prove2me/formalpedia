-- Prove2me | Theorems.Thm_JardenShami_Kappa_exists_gt_of_card_eq
-- name    : JardenShami.Kappa.exists_gt_of_card_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:41:55.903185+00:00
-- url     : https://prove2.me/theorems/131ceaf5-3880-4aa6-840b-ba1cbf09accf
-- title:
--   Kappa: exists gt of card eq
-- statement:
--   AUX: not in paper. For infinite `κ`, a subset of `κ` of size `κ` is unbounded.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L79-L85
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L79-L85

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

theorem JardenShami.Kappa.exists_gt_of_card_eq (hκ : ℵ₀ ≤ κ) {S : Set (Kappa κ)} (hS : #S = κ)
    (x : Kappa κ) : ∃ y ∈ S, x < y := by sorry
