-- Prove2me | Theorems.Thm_JardenShami_treeExp_le_power
-- name    : JardenShami.treeExp_le_power
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:44:15.243029+00:00
-- url     : https://prove2.me/theorems/bfdf3d76-2f4f-4e51-8b97-d8d1e8ce3fa9
-- title:
--   Jarden Shami: tree Exp le power
-- statement:
--   **Remark 6.2** (Section 6, `\label{remark tree exponent leq exponent}`). For every infinite
--   cardinal `λ` and every cardinal `μ`: `λ^{μ,tr} ≤ λ^μ`. (The paper assumes that `μ` is infinite
--   too; this is not needed and is not assumed here.)
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section6.lean#L100-L103
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section6.lean#L100-L103

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree

theorem JardenShami.treeExp_le_power (lam μ : Cardinal.{w}) (hlam : ℵ₀ ≤ lam) :
    treeExp lam μ ≤ lam ^ μ := by sorry
