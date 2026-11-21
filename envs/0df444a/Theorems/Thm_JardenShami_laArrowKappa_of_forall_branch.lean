-- Prove2me | Theorems.Thm_JardenShami_laArrowKappa_of_forall_branch
-- name    : JardenShami.laArrowKappa_of_forall_branch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:43:02.553176+00:00
-- url     : https://prove2.me/theorems/37698d77-1fd8-4163-8deb-3de6255e1bc0
-- title:
--   Jarden Shami: la Arrow Kappa of forall branch
-- statement:
--   AUX: not in paper. Direction (1) ⇒ (2) of Lemma 5.3 for every regular `κ` (also `κ = ℵ₀`;
--   the proof of Lemma 5.3 does not use that `κ` is uncountable).
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L455-L537
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L455-L537

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree

theorem JardenShami.laArrowKappa_of_forall_branch (κ μ : Cardinal.{w}) (hκ : κ.IsRegular) (hμ : μ < κ)
    (h1 : ∀ (T : Type w) [PartialOrder T] [IsTree T], height T = κ.ord →
        (∀ α : Ordinal.{w}, #(Lev T α) ≤ μ) → ∃ b : Set T, IsBranch b ∧ #b = κ) :
    LaArrowKappa κ μ := by sorry
