-- Prove2me | Theorems.Thm_JardenShami_ht_histFun
-- name    : JardenShami.ht_histFun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:43:22.019204+00:00
-- url     : https://prove2.me/theorems/57f4173d-3df5-44a9-80f3-058f90ae71c0
-- title:
--   Jarden Shami: ht hist Fun
-- statement:
--   **After Definition 4.2** (Section 4, unnumbered, "as `ht(f_t,F_T) = ht(t,T)`"). The height
--   of `f_t` in `F_T` equals the height of `t` in `T` (the two heights live in different universes,
--   hence the `lift`).
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L316-L336
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L316-L336

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

theorem JardenShami.ht_histFun (t : T) :
    ht (⟨histFun t, t, rfl⟩ : HistoryTree T) = Ordinal.lift.{w + 1} (ht t) := by sorry
