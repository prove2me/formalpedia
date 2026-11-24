-- Prove2me | Theorems.Thm_GlobalTheory_Cris_IsMor_of_dividedPowersZeroIdeal
-- name    : GlobalTheory.Cris.IsMor.of_dividedPowersZeroIdeal
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T09:23:54.331591+00:00
-- url     : https://prove2.me/theorems/aabe5abb-f9c7-4039-ac03-59e742a2c3b2
-- title:
--   Is Mor: of divided Powers Zero Ideal
-- statement:
--   The Is Mor construction uses the of divided Powers Zero Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/Pullback1MemHodgeFiltration.lean#L328-L329
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/Pullback1MemHodgeFiltration.lean#L328-L329

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_Pullback1MemHodgeFiltration
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

theorem GlobalTheory.Cris.IsMor.of_dividedPowersZeroIdeal {s : X ⟶ Sp R} (γ' : DividedPowers I') {s' : X' ⟶ Sp R'} {σ : R →+* R'}
    {φ : X' ⟶ X} (h : φ ≫ s = s' ≫ spMap σ) : IsMor (dp0 R) s γ' s' σ φ := by sorry
