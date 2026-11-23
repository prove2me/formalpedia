-- Prove2me | Theorems.Thm_GlobalTheory_CatCoh_Desc_Sep_mono
-- name    : GlobalTheory.CatCoh.Desc.Sep.mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:21:06.196042+00:00
-- url     : https://prove2.me/theorems/aea5caaf-046c-4067-b8db-4f8e068eb7ac
-- title:
--   Sep: mono
-- statement:
--   The Sep construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/VanishingH1InvertingMorphisms.lean#L199-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/VanishingH1InvertingMorphisms.lean#L199-L199

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
variable {F} {T : C} {P Q : ∀ S, (T ⟶ S) → Prop} (hPQ : ∀ S u, P S u → Q S u)
  (hQ : ∀ S S' u (ψ : S ⟶ S'), Q S u → Q S' (u ≫ ψ))
  (sep : ∀ S u, Q S u → Sep F fun S' (ψ : S ⟶ S') ↦ P S' (u ≫ ψ))
  (glue : ∀ S u, Q S u → Glue F fun S' (ψ : S ⟶ S') ↦ P S' (u ≫ ψ))
  (van : ∀ S u, Q S u → Van1 F fun S' (ψ : S ⟶ S') ↦ P S' (u ≫ ψ))
include hPQ

theorem GlobalTheory.CatCoh.Desc.Sep.mono (h : Sep F P) : Sep F Q := by sorry
