-- Prove2me | Theorems.Thm_GlobalTheory_CatCoh_Desc_pull2_bijective
-- name    : GlobalTheory.CatCoh.Desc.pull2_bijective
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:05:49.762235+00:00
-- url     : https://prove2.me/theorems/a3de0479-3a9b-4e04-833d-426f59b7c13e
-- title:
--   Desc: pull2 bijective
-- statement:
--   The Desc construction uses the pull2 bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/VanishingH1InvertingMorphisms.lean#L554-L561
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/VanishingH1InvertingMorphisms.lean#L554-L561

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

theorem GlobalTheory.CatCoh.Desc.pull2_bijective (H : HasLoc F) (P : ObjectProperty C) (hP : ∀ S S', (S ⟶ S') → P S → P S')
    (cov : ∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧
      ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → P S) :
    Function.Bijective (CoefMap.restrict F P.ι).pull2 := by sorry
