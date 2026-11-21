-- Prove2me | Theorems.Thm_JardenShami_card_lev_treeOfColoring_le
-- name    : JardenShami.card_lev_treeOfColoring_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:45:22.87898+00:00
-- url     : https://prove2.me/theorems/19cc75fe-09b7-4f22-9d76-c3c49385f891
-- title:
--   Jarden Shami: card lev tree Of Coloring le
-- statement:
--   **Claim 5.4** (Section 5, inside the proof of Lemma 5.3, direction (1) ⇒ (2)). For an
--   uncountable cardinal `κ` and a locally additive `C : [κ]^2 → μ`, all the levels of `T(C)` have
--   size `≤ μ`. (The paper works under the hypotheses of Lemma 5.3; of these, `κ` regular and
--   `μ < κ` are not needed and are not assumed here.)
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L431-L434
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L431-L434

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree

theorem JardenShami.card_lev_treeOfColoring_le (κ μ : Cardinal.{w}) (hunc : ℵ₀ < κ)
    (C : Coloring (Kappa κ) (Kappa μ)) (hC : IsLocallyAdditive C) :
    ∀ β : Ordinal.{w}, #(Lev (treeOfColoring C) β) ≤ μ := by sorry
