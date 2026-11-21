-- Prove2me | Theorems.Thm_JardenShami_IsLocallyAdditive_color_eq_of_le
-- name    : JardenShami.IsLocallyAdditive.color_eq_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:44:03.266192+00:00
-- url     : https://prove2.me/theorems/4631c983-f6f3-497c-8848-066e06ddad91
-- title:
--   Is Locally Additive: color eq of le
-- statement:
--   AUX: not in paper. For a locally additive `C`, `C(a,δ) = C(a,δ')` implies
--   `C(α,δ) = C(α,δ')` for all `α ≤ a`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L133-L142
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section5.lean#L133-L142

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

theorem JardenShami.IsLocallyAdditive.color_eq_of_le {A : Type w} [LinearOrder A] {D : Type*}
    {C : Coloring A D} (hC : IsLocallyAdditive C) {a δ δ' α : A} (ha : a < δ) (ha' : a < δ')
    (h : C.color a δ ha = C.color a δ' ha') (hα : α ≤ a) :
    C.color α δ (hα.trans_lt ha) = C.color α δ' (hα.trans_lt ha') := by sorry
