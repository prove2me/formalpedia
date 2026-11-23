-- Prove2me | Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyTwo_eq_of_natTrans
-- name    : GlobalTheory.CatCoh.CoefMap.pullCohomologyTwo_eq_of_natTrans
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:08:17.987968+00:00
-- url     : https://prove2.me/theorems/f6785a6e-4d4b-457f-9d2d-afa2a5d11b72
-- title:
--   Coef Map: pull Cohomology Two eq of nat Trans
-- statement:
--   The Coef Map construction uses the pull Cohomology Two eq of nat Trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CommAlgFunctorCoboundaryZeroMemCocyclesOne.lean#L321-L341
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/CommAlgFunctorCoboundaryZeroMemCocyclesOne.lean#L321-L341

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

theorem GlobalTheory.CatCoh.CoefMap.pullCohomologyTwo_eq_of_natTrans {σ' : R →+* R'} (m' : CoefMap σ' F F') (θ : m.G ⟶ m'.G)
    (h : ∀ T b, m'.α T (mp F (θ.app T) b) = m.α T b) (c : H2 F) : m.pull2 c = m'.pull2 c := by sorry
