-- Prove2me | Theorems.Thm_GlobalTheory_isIntegral_and_isNormalScheme_of_smooth
-- name    : GlobalTheory.isIntegral_and_isNormalScheme_of_smooth
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:27:58.788381+00:00
-- url     : https://prove2.me/theorems/a2b1429a-639c-4f6d-b578-16b5bf4c5866
-- title:
--   Global Theory: is Integral and is Normal Scheme of smooth
-- statement:
--   The Global Theory construction uses the is Integral and is Normal Scheme of smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsIntegralAndIsNormalSchemeOfSmoothDvr.lean#L36-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/IsIntegralAndIsNormalSchemeOfSmoothDvr.lean#L36-L46

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

theorem GlobalTheory.isIntegral_and_isNormalScheme_of_smooth (T K : Type) [CommRing T] [IsDomain T]
    [IsNoetherianRing T] [IsIntegrallyClosed T] [Field K] [Algebra T K] [IsFractionRing T K]
    {X : Scheme.{0}} (f : X ⟶ Sp T) [Smooth f]
    [ConnectedSpace ↥(pullback f (spMap (algebraMap T K)))] :
    IsIntegral X ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X := by sorry
