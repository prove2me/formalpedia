-- Prove2me | Theorems.Thm_JardenShami_mem_succPart_historyTree
-- name    : JardenShami.mem_succPart_historyTree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:43:24.274775+00:00
-- url     : https://prove2.me/theorems/ac8c74bf-9300-4d52-a098-9c936ba2391f
-- title:
--   Jarden Shami: mem succ Part history Tree
-- statement:
--   **After Definition 4.2** (Section 4, unnumbered, "Clearly"). `(F_T)^succ = ({f_t : t ∈
--   T^succ}, ⊆)`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L340-L362
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L340-L362

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

theorem JardenShami.mem_succPart_historyTree (g : HistoryTree T) :
    g ∈ succPart (HistoryTree T) ↔ ∃ t ∈ succPart T, g.1 = histFun t := by sorry
