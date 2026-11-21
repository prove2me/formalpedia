-- Prove2me | Theorems.Thm_JardenShami_Enumeration_ht_t
-- name    : JardenShami.Enumeration.ht_t
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:41:31.599052+00:00
-- url     : https://prove2.me/theorems/a8d07896-f347-49f2-ac69-61529df2938d
-- title:
--   Enumeration: ht t
-- statement:
--   AUX: not in paper. `ht(t^i_α) = α`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L768-L770
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L768-L770

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

theorem JardenShami.Enumeration.ht_t (e : Enumeration κ T) {α i : Ordinal.{w}} (hα : α < κ.ord)
    (hi : i < (#(Lev T α)).ord) : ht (e.t α i) = α := by sorry
