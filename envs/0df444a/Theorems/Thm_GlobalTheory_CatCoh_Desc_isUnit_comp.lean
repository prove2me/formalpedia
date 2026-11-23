-- Prove2me | Theorems.Thm_GlobalTheory_CatCoh_Desc_isUnit_comp
-- name    : GlobalTheory.CatCoh.Desc.isUnit_comp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:26:32.714304+00:00
-- url     : https://prove2.me/theorems/f98e3cdf-5301-4aa4-a11a-4b97f5235fcd
-- title:
--   Desc: is Unit comp
-- statement:
--   The Desc construction uses the is Unit comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/VanishingH1InvertingMorphisms.lean#L458-L460
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/VanishingH1InvertingMorphisms.lean#L458-L460

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Filter
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.CatCoh.Desc
universe v u w
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ CommAlgCat.{0} R)
variable {F} (H : HasLoc F) {T : C} {ι : Type} [Fintype ι] {b : ι → F.obj T}
  (hb : Ideal.span (Set.range b) = ⊤)
omit [Fintype ι]

theorem GlobalTheory.CatCoh.Desc.isUnit_comp {S S' : C} {u : T ⟶ S} (ψ : S ⟶ S') {x : F.obj T} (h : IsUnit (mp F u x)) :
    IsUnit (mp F (u ≫ ψ) x) := by sorry
