-- Prove2me | Theorems.Thm_GlobalTheory_ThickDiv_cst_dvd_gs_of_app_eq_zero
-- name    : GlobalTheory.ThickDiv.cst_dvd_gs_of_app_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:04:29.056773+00:00
-- url     : https://prove2.me/theorems/2430b655-6bc9-4986-9c4c-14298412f2b0
-- title:
--   Thick Div: cst dvd gs of app eq zero
-- statement:
--   The Thick Div construction uses the cst dvd gs of app eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/DvdOfAppEqZeroOfIsAffineOpen.lean#L70-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/DvdOfAppEqZeroOfIsAffineOpen.lean#L70-L86

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

theorem GlobalTheory.ThickDiv.cst_dvd_gs_of_app_eq_zero (hϖ : Irreducible ϖ) (X : Over (Spec (CommRingCat.of V))) [Flat X.hom]
    (e : ℕ) (W : X.left.Opens) (f : Γ(X.left, W))
    (hf : ((fstG (maximalIdeal V) e X).left.app W).hom f = 0) (x : X.left) (hx : x ∈ W) :
    cst X.hom x (ϖ ^ (e + 1)) ∣ gs (𝟙 X.left) x W f := by sorry
