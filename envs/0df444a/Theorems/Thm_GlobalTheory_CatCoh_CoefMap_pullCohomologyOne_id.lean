-- Prove2me | Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyOne_id
-- name    : GlobalTheory.CatCoh.CoefMap.pullCohomologyOne_id
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:08:34.700476+00:00
-- url     : https://prove2.me/theorems/e7c5e53f-e702-4a5c-b154-c7066f482f10
-- title:
--   Coef Map: pull Cohomology One id
-- statement:
--   The Coef Map construction uses the pull Cohomology One id property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CommAlgFunctorCoboundaryZeroMemCocyclesOne.lean#L289-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CommAlgFunctorCoboundaryZeroMemCocyclesOne.lean#L289-L291

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
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']
  {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {C'' : Type u''} [Category.{v''} C'']
open GlobalTheory.CatCoh.CoefMap
variable {σ : R →+* R'} {τ : R' →+* R''} {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R'}
  {F'' : C'' ⥤ CommAlgCat.{0} R''}
variable (m : CoefMap σ F F')

theorem GlobalTheory.CatCoh.CoefMap.pullCohomologyOne_id (c : H1 F) : (id F).pull1 c = c := by sorry
