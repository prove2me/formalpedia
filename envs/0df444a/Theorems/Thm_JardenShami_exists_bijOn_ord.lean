-- Prove2me | Theorems.Thm_JardenShami_exists_bijOn_ord
-- name    : JardenShami.exists_bijOn_ord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:42:47.709176+00:00
-- url     : https://prove2.me/theorems/68b0944f-5f94-4e5f-aa5e-dd4b60581bc9
-- title:
--   Jarden Shami: exists bij On ord
-- statement:
--   AUX: not in paper. A nonempty set `L` has a bijective enumeration
--   `⟨f(i) : i < |L|⟩` starting with a prescribed element `c ∈ L`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L888-L912
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section4.lean#L888-L912

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
omit [PartialOrder T] [IsTree T]

theorem JardenShami.exists_bijOn_ord {L : Set T} {c : T} (hc : c ∈ L) :
    ∃ f : Ordinal.{w} → T, Set.BijOn f (Set.Iio (#L).ord) L ∧ f 0 = c := by sorry
