-- Prove2me | Theorems.Thm_JardenShami_exists_nonsplitting
-- name    : JardenShami.exists_nonsplitting
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:44:36.980328+00:00
-- url     : https://prove2.me/theorems/7e4150d4-6b0d-4c71-9035-59ee79ec73d3
-- title:
--   Jarden Shami: exists nonsplitting
-- statement:
--   AUX: not in paper. In a well-pruned `κ`-tree (`κ` regular) whose levels have size `< λ`,
--   `λ < κ`, some node `a` does not split: any two nodes above `a` of the same height are equal.
--   (Replaces Cases A and B of the paper's proof of Claim 7.8: the level sizes are eventually a constant
--   `n < λ`; for finite `n` the restriction maps are bijective, and for infinite `n` the diagonal
--   argument of Claim 7.9 (`le_mk_lev_of_splitting`) at a level closed under splitting and of
--   cofinality `≥ n⁺` (`exists_closed_level`) gives a level of size `≥ n⁺`.)
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L785-L845
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L785-L845

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7
set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree

theorem JardenShami.exists_nonsplitting {κ lam : Cardinal.{w}} (hκ : κ.IsRegular) (hlam : lam < κ)
    {T : Type w} [PartialOrder T] [IsTree T] (hT : IsKappaTree κ T) (hwp : WellPruned T)
    (hlev : ∀ α : Ordinal.{w}, #(Lev T α) < lam) :
    ∃ a : T, ∀ b c : T, a < b → a < c → ht b = ht c → b = c := by sorry
