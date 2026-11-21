-- Prove2me | Theorems.Thm_JardenShami_mem_histFun
-- name    : JardenShami.mem_histFun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:44:43.489295+00:00
-- url     : https://prove2.me/theorems/97e5266d-07f8-492e-80fa-817f4c6aa7e1
-- title:
--   Jarden Shami: mem hist Fun
-- statement:
--   AUX: not in paper. Membership in the graph of `f_s`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L260-L261
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L260-L261

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

theorem JardenShami.mem_histFun {s p : T} {α : Ordinal.{w}} : (α, p) ∈ histFun s ↔ p < s ∧ ht p = α := by sorry
