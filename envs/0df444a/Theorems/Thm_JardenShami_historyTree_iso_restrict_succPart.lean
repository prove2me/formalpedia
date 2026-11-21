-- Prove2me | Theorems.Thm_JardenShami_historyTree_iso_restrict_succPart
-- name    : JardenShami.historyTree_iso_restrict_succPart
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:43:38.601185+00:00
-- url     : https://prove2.me/theorems/d406a4f5-a102-4c87-b9c0-1c5d734400fc
-- title:
--   Jarden Shami: history Tree iso restrict succ Part
-- statement:
--   **Remark 4.3** (Section 4, `\label{remark 3.3}`). If `g : F_T → F_S` is an isomorphism,
--   then `g ↾ (F_T)^succ` is an isomorphism from `(F_T)^succ` to `(F_S)^succ`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L421-L429
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L421-L429

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open Tree
variable {T : Type w} [PartialOrder T] [IsTree T]

theorem JardenShami.historyTree_iso_restrict_succPart {S : Type w} [PartialOrder S] [IsTree S]
    (g : HistoryTree T ≃o HistoryTree S) :
    ∃ g' : succPart (HistoryTree T) ≃o succPart (HistoryTree S),
      ∀ x : succPart (HistoryTree T), (g' x : HistoryTree S) = g x := by sorry
