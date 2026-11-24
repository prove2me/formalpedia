-- Prove2me | Theorems.Thm_GlobalTheory_isIntegral_of_flat_of_isIntegral_genericFibre
-- name    : GlobalTheory.isIntegral_of_flat_of_isIntegral_genericFibre
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:57:11.114228+00:00
-- url     : https://prove2.me/theorems/863bd366-a222-4577-b24c-fdcf506b2d2e
-- title:
--   Global Theory: is Integral of flat of is Integral generic Fibre
-- statement:
--   The Global Theory construction uses the is Integral of flat of is Integral generic Fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsOpenImmersionSpMapOfIsDiscreteValuationRing.lean#L30-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsOpenImmersionSpMapOfIsDiscreteValuationRing.lean#L30-L43

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIntegralAndIsNormalSchemeOfSmoothDvr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIsoOfIsOpenImmersionOfGeometricallyConnected
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenImmersionSpMapOfIsDiscreteValuationRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory

theorem GlobalTheory.isIntegral_of_flat_of_isIntegral_genericFibre (T K : Type) [CommRing T] [IsDomain T]
    [Field K] [Algebra T K] [IsFractionRing T K] {X : Scheme.{0}} (f : X ⟶ Sp T) [Flat f]
    [IsIntegral (pullback f (spMap (algebraMap T K)))] : IsIntegral X := by sorry
