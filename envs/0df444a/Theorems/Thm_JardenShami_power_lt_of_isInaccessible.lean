-- Prove2me | Theorems.Thm_JardenShami_power_lt_of_isInaccessible
-- name    : JardenShami.power_lt_of_isInaccessible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:44:22.026009+00:00
-- url     : https://prove2.me/theorems/b0d1292f-fe50-47e2-996e-681524e93fc9
-- title:
--   Jarden Shami: power lt of is Inaccessible
-- statement:
--   AUX: not in paper. For an inaccessible `κ` and `λ, μ < κ`: `λ^μ < κ`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section6.lean#L131-L135
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section6.lean#L131-L135

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree

theorem JardenShami.power_lt_of_isInaccessible {κ lam μ : Cardinal.{w}} (hκ : κ.IsInaccessible)
    (hlam : lam < κ) (hμ : μ < κ) : lam ^ μ < κ := by sorry
