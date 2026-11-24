-- Prove2me | Theorems.Thm_GlobalTheory_ThickDiv_dvd_of_app_eq_zero_of_isAffineOpen
-- name    : GlobalTheory.ThickDiv.dvd_of_app_eq_zero_of_isAffineOpen
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:07:48.137831+00:00
-- url     : https://prove2.me/theorems/36fbfc19-a993-4193-86c4-e07017c04860
-- title:
--   Thick Div: dvd of app eq zero of is Affine Open
-- statement:
--   The Thick Div construction uses the dvd of app eq zero of is Affine Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/DvdOfAppEqZeroOfIsAffineOpen.lean#L61-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/DvdOfAppEqZeroOfIsAffineOpen.lean#L61-L68

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_DvdOfAppEqZeroOfIsAffineOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThickDiv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}

theorem GlobalTheory.ThickDiv.dvd_of_app_eq_zero_of_isAffineOpen (hϖ : Irreducible ϖ) (X : Over (Spec (CommRingCat.of V))) [Flat X.hom]
    (e : ℕ) {U : X.left.Opens} (hU : IsAffineOpen U) (f : Γ(X.left, U))
    (hf : ((fstG (maximalIdeal V) e X).left.app U).hom f = 0) : constFn X.hom U (ϖ ^ (e + 1)) ∣ f := by sorry
