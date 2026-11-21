-- Prove2me | Theorems.Thm_JardenShami_not_isAronszajn_of_card_lev_lt
-- name    : JardenShami.not_isAronszajn_of_card_lev_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:44:39.970954+00:00
-- url     : https://prove2.me/theorems/9fc73239-f38c-43b8-83f5-9a1041b189a0
-- title:
--   Jarden Shami: not is Aronszajn of card lev lt
-- statement:
--   **Claim 7.8** (Section 7, `\label{the exercise of kunen}`; recalled from
--   [Large, Proposition 7.9] and proved in the paper "for completeness"). Let `κ` and `λ` be cardinals
--   such that `κ` is regular and `λ < κ`. If `T` is a `κ`-tree whose levels have size `< λ`, then
--   `T` is not `κ`-Aronszajn.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L859-L909
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L859-L909

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7
set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree

theorem JardenShami.not_isAronszajn_of_card_lev_lt (κ lam : Cardinal.{w})
    (hκ : κ.IsRegular) (hlam : lam < κ) (T : Type w) [PartialOrder T] [IsTree T]
    (hT : IsKappaTree κ T) (hlev : ∀ α : Ordinal.{w}, #(Lev T α) < lam) :
    ¬ IsAronszajn κ T := by sorry
