-- Prove2me | Theorems.Thm_JardenShami_exists_le_ht_eq
-- name    : JardenShami.exists_le_ht_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:43:11.623095+00:00
-- url     : https://prove2.me/theorems/5988fb11-412d-4adc-af2b-20dca96c6c4a
-- title:
--   Jarden Shami: exists le ht eq
-- statement:
--   AUX: not in paper. Every node lies above a node of each smaller level.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L342-L346
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section7.lean#L342-L346

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section6
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section7
set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami
open Tree
variable {T : Type w} [PartialOrder T] [IsTree T]

theorem JardenShami.exists_le_ht_eq {t : T} {α : Ordinal.{w}} (h : α ≤ ht t) : ∃ s ≤ t, ht s = α := by sorry
