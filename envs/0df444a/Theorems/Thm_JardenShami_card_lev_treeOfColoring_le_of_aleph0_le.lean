-- Prove2me | Theorems.Thm_JardenShami_card_lev_treeOfColoring_le_of_aleph0_le
-- name    : JardenShami.card_lev_treeOfColoring_le_of_aleph0_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:42:55.684202+00:00
-- url     : https://prove2.me/theorems/dd96a9e8-33fe-492b-bbb7-d3c1d8f251db
-- title:
--   Jarden Shami: card lev tree Of Coloring le of aleph0 le
-- statement:
--   AUX: not in paper. Claim 5.4 for every infinite `κ` (neither regularity nor uncountability
--   nor `μ < κ` is needed; the proof of Claim 5.4 uses only that there is a color).
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L318-L425
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L318-L425

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree

theorem JardenShami.card_lev_treeOfColoring_le_of_aleph0_le (κ μ : Cardinal.{w}) (hκ0 : ℵ₀ ≤ κ)
    (C : Coloring (Kappa κ) (Kappa μ)) (hC : IsLocallyAdditive C) :
    ∀ β : Ordinal.{w}, #(Lev (treeOfColoring C) β) ≤ μ := by sorry
