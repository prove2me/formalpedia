-- Prove2me | Theorems.Thm_JardenShami_Kappa_exists_gt
-- name    : JardenShami.Kappa.exists_gt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:43:14.090315+00:00
-- url     : https://prove2.me/theorems/9a6605d9-5517-427c-a754-9cc4083bdfea
-- title:
--   Kappa: exists gt
-- statement:
--   AUX: not in paper. For infinite `κ`, `κ` has no largest element.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L83-L86
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L83-L86

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7
set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree

theorem JardenShami.Kappa.exists_gt {κ : Cardinal.{w}} (hκ : ℵ₀ ≤ κ) (x : Kappa κ) : ∃ y, x < y := by sorry
