-- Prove2me | Theorems.Thm_JardenShami_not_starLaArrowKappa_of_succ_eq
-- name    : JardenShami.not_starLaArrowKappa_of_succ_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:45:43.406913+00:00
-- url     : https://prove2.me/theorems/15274482-631e-426e-adff-202ce4b0250c
-- title:
--   Jarden Shami: not star La Arrow Kappa of succ eq
-- statement:
--   **Proposition 7.5** (Section 7, `\label{proposition mu^+<kappa can's be omitted}`).
--   `κ → (κ)_{*-la_μ}` does not hold if `μ⁺ = κ`. The standing assumption `κ = cf(κ)` of Subsection
--   7.1 is kept as `κ.IsRegular` (with Mathlib's definition this makes `κ`, hence `μ`, infinite; see
--   FIDELITY.md: for `μ ≤ 1` the statement without it is false).
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L258-L318
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L258-L318

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7
set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree

theorem JardenShami.not_starLaArrowKappa_of_succ_eq (κ μ : Cardinal.{w}) (hκ : κ.IsRegular)
    (h : Order.succ μ = κ) : ¬ StarLaArrowKappa κ μ := by sorry
