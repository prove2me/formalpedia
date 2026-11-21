-- Prove2me | Theorems.Thm_JardenShami_laArrowKappa_of_succ_lt
-- name    : JardenShami.laArrowKappa_of_succ_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:45:54.334302+00:00
-- url     : https://prove2.me/theorems/2f8ff0de-9ce5-42fa-9314-37ebc2241f01
-- title:
--   Jarden Shami: la Arrow Kappa of succ lt
-- statement:
--   **Theorem 7.7** (Section 7, `\label{the only theorem}`). Let `κ` be a regular cardinal and
--   `μ` a cardinal with `μ⁺ < κ`. Then `κ → (κ)_{la_μ}` (in the sense of Section 5,
--   `LaArrowKappa`).
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L914-L925
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L914-L925

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7
set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree

theorem JardenShami.laArrowKappa_of_succ_lt (κ μ : Cardinal.{w})
    (hκ : κ.IsRegular) (h : Order.succ μ < κ) : LaArrowKappa κ μ := by sorry
