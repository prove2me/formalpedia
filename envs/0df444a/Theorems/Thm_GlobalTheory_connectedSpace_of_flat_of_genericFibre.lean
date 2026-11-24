-- Prove2me | Theorems.Thm_GlobalTheory_connectedSpace_of_flat_of_genericFibre
-- name    : GlobalTheory.connectedSpace_of_flat_of_genericFibre
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:13:19.236842+00:00
-- url     : https://prove2.me/theorems/260ebc7a-eb0b-4162-bb8e-3d947ed47cbd
-- title:
--   Global Theory: connected Space of flat of generic Fibre
-- statement:
--   The Global Theory construction uses the connected Space of flat of generic Fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsIntegralAndIsNormalSchemeOfSmoothDvr.lean#L27-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsIntegralAndIsNormalSchemeOfSmoothDvr.lean#L27-L34

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIntegralAndIsNormalSchemeOfSmoothDvr
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

theorem GlobalTheory.connectedSpace_of_flat_of_genericFibre (T K : Type) [CommRing T] [IsDomain T] [Field K]
    [Algebra T K] [IsFractionRing T K] {X : Scheme.{0}} (f : X ⟶ Sp T) [Flat f]
    [ConnectedSpace ↥(pullback f (spMap (algebraMap T K)))] : ConnectedSpace X := by sorry
