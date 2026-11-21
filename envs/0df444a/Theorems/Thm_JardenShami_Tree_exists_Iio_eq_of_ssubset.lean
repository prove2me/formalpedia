-- Prove2me | Theorems.Thm_JardenShami_Tree_exists_Iio_eq_of_ssubset
-- name    : JardenShami.Tree.exists_Iio_eq_of_ssubset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:43:03.889378+00:00
-- url     : https://prove2.me/theorems/53bb4296-0cfd-438e-a840-501fb4da6aae
-- title:
--   Tree: exists Iio eq of ssubset
-- statement:
--   AUX: not in paper. If `Iio s ⊂ Iio t` then `Iio s = Iio u` for some `u < t`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L165-L176
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L165-L176

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
import Mathlib.Data.Sym.Sym2.Order
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
set_option autoImplicit true
open Cardinal
universe u v w
noncomputable section
open JardenShami
open JardenShami.Tree
variable {T : Type w} [PartialOrder T] [IsTree T]

theorem JardenShami.Tree.exists_Iio_eq_of_ssubset {s t : T} (h : Set.Iio s ⊂ Set.Iio t) :
    ∃ u < t, Set.Iio s = Set.Iio u := by sorry
