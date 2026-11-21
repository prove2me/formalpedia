-- Prove2me | Theorems.Thm_JardenShami_noAronszajn_succ_iff_laArrowKappa
-- name    : JardenShami.noAronszajn_succ_iff_laArrowKappa
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:45:24.384885+00:00
-- url     : https://prove2.me/theorems/b3418a76-70fb-4948-ae29-1182caf08ea5
-- title:
--   Jarden Shami: no Aronszajn succ iff la Arrow Kappa
-- statement:
--   **Theorem 5.2** (Section 5, `\label{theorem 4.2}`). For every infinite cardinal `μ` the
--   following are equivalent: (1) there exists no `μ⁺`-Aronszajn tree; (2) `μ⁺ → (μ⁺)_{la_μ}`, namely
--   every locally additive coloring `C : [μ⁺]^2 → μ` admits a homogeneous set of size `μ⁺`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L628-L651
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L628-L651

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree

theorem JardenShami.noAronszajn_succ_iff_laArrowKappa (μ : Cardinal.{w}) (hμ : ℵ₀ ≤ μ) :
    NoAronszajn (Order.succ μ) ↔ LaArrowKappa (Order.succ μ) μ := by sorry
