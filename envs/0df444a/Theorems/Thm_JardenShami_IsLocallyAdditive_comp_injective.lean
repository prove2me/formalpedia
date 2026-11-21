-- Prove2me | Theorems.Thm_JardenShami_IsLocallyAdditive_comp_injective
-- name    : JardenShami.IsLocallyAdditive.comp_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:44:07.228208+00:00
-- url     : https://prove2.me/theorems/a6924406-012d-4210-b9bb-742c757a9374
-- title:
--   Is Locally Additive: comp injective
-- statement:
--   AUX: not in paper. Composing a locally additive coloring with an injective map of colors
--   gives a locally additive coloring.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L153-L156
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L153-L156

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section4
import Mathlib.SetTheory.Cardinal.Pigeonhole
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section5
set_option autoImplicit true
open Cardinal
universe w
noncomputable section
open JardenShami
open Tree
variable {κ : Cardinal.{w}}

theorem JardenShami.IsLocallyAdditive.comp_injective {A : Type w} [LinearOrder A] {D E : Type*}
    {C : Coloring A D} (hC : IsLocallyAdditive C) {ι : D → E} (hι : Function.Injective ι) :
    IsLocallyAdditive (ι ∘ C) := by sorry
