-- Prove2me | Theorems.Thm_GlobalTheory_CatCoh_H1_mk_eq_mk
-- name    : GlobalTheory.CatCoh.H1.mk_eq_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:04:54.06592+00:00
-- url     : https://prove2.me/theorems/01bc0153-5c92-4753-a705-2cfa036ad1f9
-- title:
--   H1: mk eq mk
-- statement:
--   The H1 construction uses the mk eq mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CommAlgFunctorCoboundaryZeroMemCocyclesOne.lean#L149-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CommAlgFunctorCoboundaryZeroMemCocyclesOne.lean#L149-L151

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

theorem GlobalTheory.CatCoh.H1.mk_eq_mk {f f' : Z1 F} : H1.mk F f = H1.mk F f' ↔ ∃ g, d0 F g = f.1 - f'.1 := by sorry
