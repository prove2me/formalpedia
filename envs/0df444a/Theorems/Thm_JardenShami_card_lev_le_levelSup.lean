-- Prove2me | Theorems.Thm_JardenShami_card_lev_le_levelSup
-- name    : JardenShami.card_lev_le_levelSup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:43:47.965332+00:00
-- url     : https://prove2.me/theorems/9dad9878-fcb3-42b5-9891-24dbb5fa25e9
-- title:
--   Jarden Shami: card lev le level Sup
-- statement:
--   AUX: not in paper. `μ_α ≤ μ`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L821-L822
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L821-L822

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}} {T : Type w} [PartialOrder T] [IsTree T]

theorem JardenShami.card_lev_le_levelSup (α : Kappa κ) : #(Lev T (α : Ordinal.{w})) ≤ levelSup κ T := by sorry
