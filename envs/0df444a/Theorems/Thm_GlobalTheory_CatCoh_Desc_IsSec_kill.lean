-- Prove2me | Theorems.Thm_GlobalTheory_CatCoh_Desc_IsSec_kill
-- name    : GlobalTheory.CatCoh.Desc.IsSec.kill
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:25:46.393446+00:00
-- url     : https://prove2.me/theorems/df480e08-8075-4bae-91c7-63126e9c28d7
-- title:
--   Is Sec: kill
-- statement:
--   The Is Sec construction uses the kill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/VanishingH1InvertingMorphisms.lean#L325-L337
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/VanishingH1InvertingMorphisms.lean#L325-L337

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
variable {F} (H : HasLoc F) {T : C} {P : ∀ S, (T ⟶ S) → Prop} {b : F.obj T}
  (hP : ∀ S u, P S u ↔ IsUnit (mp F u b))
include H hP

theorem GlobalTheory.CatCoh.Desc.IsSec.kill (c : F.obj T) {s : ∀ S, (T ⟶ S) → F.obj S} (hs : IsSec F P s)
    (h0 : ∀ S u, P S u → IsUnit (mp F u c) → s S u = 0) :
    ∀ᶠ M : ℕ in atTop, ∀ S u, P S u → mp F u c ^ M * s S u = 0 := by sorry
