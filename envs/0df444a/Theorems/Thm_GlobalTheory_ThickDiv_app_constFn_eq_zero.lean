-- Prove2me | Theorems.Thm_GlobalTheory_ThickDiv_app_constFn_eq_zero
-- name    : GlobalTheory.ThickDiv.app_constFn_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:10:33.884719+00:00
-- url     : https://prove2.me/theorems/88d5ce3e-aeb5-4275-a3fa-399ed83db378
-- title:
--   Thick Div: app const Fn eq zero
-- statement:
--   The Thick Div construction uses the app const Fn eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/DvdOfAppEqZeroOfIsAffineOpen.lean#L26-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/DvdOfAppEqZeroOfIsAffineOpen.lean#L26-L42

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

theorem GlobalTheory.ThickDiv.app_constFn_eq_zero {V : Type} [CommRing V] [IsDomain V] (I : Ideal V) (e : ℕ)
    (X : Over (Spec (CommRingCat.of V))) (W : X.left.Opens) {a : V} (ha : a ∈ I ^ (e + 1)) :
    ((fstG I e X).left.app W).hom (constFn X.hom W a) = 0 := by sorry
