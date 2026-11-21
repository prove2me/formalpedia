-- Prove2me | Theorems.Thm_JardenShami_card_simClasses_le
-- name    : JardenShami.card_simClasses_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:44:25.144451+00:00
-- url     : https://prove2.me/theorems/403656e5-1290-4a4a-ab0b-f5d5690958d3
-- title:
--   Jarden Shami: card sim Classes le
-- statement:
--   **Lemma 7.3** (Section 7, `\label{lemma number of equivalence classes}`). Under the standing
--   assumption of Subsection 7.1: if `μ⁺ < κ` then the number of `∼`-equivalence classes is at most
--   `μ`. The classes are counted as the sets `{γ : β ∼ γ}`, `β < κ`. The part `μ < κ` of the standing
--   assumption is not a hypothesis here (it follows from `μ⁺ < κ`).
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L128-L156
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L128-L156

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7
set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree

theorem JardenShami.card_simClasses_le (κ μ : Cardinal.{w}) (hκ : κ.IsRegular)
    (C : Coloring (Kappa κ) (Kappa μ)) (hC : IsStarLocallyAdditive C)
    (h : Order.succ μ < κ) :
    #(Set.range fun β : Kappa κ => {γ : Kappa κ | Sim C β γ}) ≤ μ := by sorry
