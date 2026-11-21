-- Prove2me | Theorems.Thm_JardenShami_Iio_ssubset_Iio_of_lt
-- name    : JardenShami.Iio_ssubset_Iio_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:43:04.270174+00:00
-- url     : https://prove2.me/theorems/06efabdf-bcfd-4cbc-ba43-c484d54d28de
-- title:
--   Jarden Shami: Iio ssubset Iio of lt
-- statement:
--   AUX: not in paper. For `u < t`, `Iio u ⊂ Iio t`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L281-L282
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L281-L282

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
omit [IsTree T]

theorem JardenShami.Iio_ssubset_Iio_of_lt {u t : T} (h : u < t) : Set.Iio u ⊂ Set.Iio t := by sorry
