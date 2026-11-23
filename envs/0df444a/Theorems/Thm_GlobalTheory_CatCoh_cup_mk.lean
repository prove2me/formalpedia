-- Prove2me | Theorems.Thm_GlobalTheory_CatCoh_cup_mk
-- name    : GlobalTheory.CatCoh.cup_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:35:50.255332+00:00
-- url     : https://prove2.me/theorems/d5083b6b-b400-4f0f-9b8f-5de13651f1cc
-- title:
--   Cat Coh: cup mk
-- statement:
--   The Cat Coh construction uses the cup mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CommAlgFunctorCoboundaryZeroMemCocyclesOne.lean#L190-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CommAlgFunctorCoboundaryZeroMemCocyclesOne.lean#L190-L190

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
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
open CategoryTheory
open GlobalTheory GlobalTheory.CatCoh
universe v u v' u' v'' u''
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ CommAlgCat.{0} R)
variable {F}
variable (F)
variable {F}
variable (F)

theorem GlobalTheory.CatCoh.cup_mk (a b : Z1 F) : cup F (H1.mk F a) (H1.mk F b) = H2.mk F (cupZ F a b) := by sorry
