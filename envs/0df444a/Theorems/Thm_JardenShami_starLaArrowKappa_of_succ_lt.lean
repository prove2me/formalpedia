-- Prove2me | Theorems.Thm_JardenShami_starLaArrowKappa_of_succ_lt
-- name    : JardenShami.starLaArrowKappa_of_succ_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:45:40.882913+00:00
-- url     : https://prove2.me/theorems/a49fbc2f-2d3c-41df-949c-4a04ac3064aa
-- title:
--   Jarden Shami: star La Arrow Kappa of succ lt
-- statement:
--   **Theorem 7.4** (Section 7, `\label{theorem shelah *-locally-additive}`, after
--   [Sh42, Theorem 1.1]). `κ → (κ)_{*-la_μ}` holds whenever `μ⁺ < κ = cf(κ)`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L167-L252
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L167-L252

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7
set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree

theorem JardenShami.starLaArrowKappa_of_succ_lt (κ μ : Cardinal.{w}) (hκ : κ.IsRegular)
    (h : Order.succ μ < κ) : StarLaArrowKappa κ μ := by sorry
