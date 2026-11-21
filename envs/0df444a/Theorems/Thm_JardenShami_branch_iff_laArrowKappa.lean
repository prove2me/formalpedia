-- Prove2me | Theorems.Thm_JardenShami_branch_iff_laArrowKappa
-- name    : JardenShami.branch_iff_laArrowKappa
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:44:12.314115+00:00
-- url     : https://prove2.me/theorems/2b03e829-7913-4914-8a9d-438651a79e92
-- title:
--   Jarden Shami: branch iff la Arrow Kappa
-- statement:
--   **Lemma 5.3** (Section 5, `\label{lemma 6}`, `\label{the main lemma}`). Suppose `κ` is a
--   regular uncountable cardinal and `μ < κ`. The following are equivalent: (1) every tree of height
--   `κ` whose levels have size `≤ μ` admits a `κ`-sized branch; (2) `κ → (κ)_{la_μ}`, namely every
--   locally additive coloring `C : [κ]^2 → μ` admits a homogeneous set of size `κ`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L543-L623
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L543-L623

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree

theorem JardenShami.branch_iff_laArrowKappa (κ μ : Cardinal.{w}) (hκ : κ.IsRegular) (hunc : ℵ₀ < κ)
    (hμ : μ < κ) :
    (∀ (T : Type w) [PartialOrder T] [IsTree T], height T = κ.ord →
        (∀ α : Ordinal.{w}, #(Lev T α) ≤ μ) → ∃ b : Set T, IsBranch b ∧ #b = κ) ↔
      LaArrowKappa κ μ := by sorry
