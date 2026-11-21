-- Prove2me | Theorems.Thm_JardenShami_histFun_eq_iff
-- name    : JardenShami.histFun_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:42:38.070175+00:00
-- url     : https://prove2.me/theorems/bba2a7bc-258c-4fd7-bd9a-0c0360e1fc72
-- title:
--   Jarden Shami: hist Fun eq iff
-- statement:
--   AUX: not in paper.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L276-L277
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L276-L277

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

theorem JardenShami.histFun_eq_iff {s t : T} : histFun s = histFun t ↔ Set.Iio s = Set.Iio t := by sorry
