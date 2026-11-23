-- Prove2me | Theorems.Thm_GlobalTheory_Cris_IsMor_pullCohomologyTwo_cup
-- name    : GlobalTheory.Cris.IsMor.pullCohomologyTwo_cup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:47:19.048032+00:00
-- url     : https://prove2.me/theorems/46f278e8-9d9e-4d11-bd8d-8a62f5d33af2
-- title:
--   Is Mor: pull Cohomology Two cup
-- statement:
--   The Is Mor construction uses the pull Cohomology Two cup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/Pullback1MemHodgeFiltration.lean#L269-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/Pullback1MemHodgeFiltration.lean#L269-L270

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_Pullback1MemHodgeFiltration
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyTwo_cup

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
open CategoryTheory AlgebraicGeometry DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory GlobalTheory.Cris
open CatCoh
variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {I : Ideal R} {I' : Ideal R'}
  {I'' : Ideal R''} {X X' X'' : Scheme.{0}}
attribute [instance] Thick.ring Thick.alg Thick.ring₀
variable {γ : DividedPowers I} {γ' : DividedPowers I'} {γ'' : DividedPowers I''}
  {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''}
variable {σ : R →+* R'} {φ : X' ⟶ X}

theorem GlobalTheory.Cris.IsMor.pullCohomologyTwo_cup (h : IsMor γ s γ' s' σ φ) (a b : H1 γ s) :
    h.pull2 (cup _ a b) = cup _ (h.pull1 a) (h.pull1 b) := by sorry
