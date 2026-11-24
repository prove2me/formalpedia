-- Prove2me | Theorems.Thm_GlobalTheory_isReduced_scheme_of_smooth_of_isIntegrallyClosed
-- name    : GlobalTheory.isReduced_scheme_of_smooth_of_isIntegrallyClosed
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:42:21.866321+00:00
-- url     : https://prove2.me/theorems/daa27db7-5611-4401-818e-b898f9f44ccd
-- title:
--   Global Theory: is Reduced scheme of smooth of is Integrally Closed
-- statement:
--   The Global Theory construction uses the is Reduced scheme of smooth of is Integrally Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsReducedSchemeOfSmoothOfIsIntegrallyClosed.lean#L13-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsReducedSchemeOfSmoothOfIsIntegrallyClosed.lean#L13-L19

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsReducedSchemeOfSmoothOfIsIntegrallyClosed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory

theorem GlobalTheory.isReduced_scheme_of_smooth_of_isIntegrallyClosed (T : Type) [CommRing T] [IsDomain T]
    [IsIntegrallyClosed T] {X : Scheme.{0}} (f : X ⟶ Sp T) [Smooth f] :
    AlgebraicGeometry.IsReduced X := by sorry
