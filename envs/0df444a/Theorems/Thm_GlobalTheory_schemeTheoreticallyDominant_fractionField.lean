-- Prove2me | Theorems.Thm_GlobalTheory_schemeTheoreticallyDominant_fractionField
-- name    : GlobalTheory.schemeTheoreticallyDominant_fractionField
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:54:07.798433+00:00
-- url     : https://prove2.me/theorems/eec2e005-16eb-46a7-88a5-c9de2c08779b
-- title:
--   Global Theory: scheme Theoretically Dominant fraction Field
-- statement:
--   The Global Theory construction uses the scheme Theoretically Dominant fraction Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLiftOfSchemeTheoreticallyDominant.lean#L112-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLiftOfSchemeTheoreticallyDominant.lean#L112-L126

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLiftOfSchemeTheoreticallyDominant
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

theorem GlobalTheory.schemeTheoreticallyDominant_fractionField (T K : Type) [CommRing T] [IsDomain T] [Field K]
    [Algebra T K] [IsFractionRing T K] :
    IsSchemeTheoreticallyDominant (spMap (algebraMap T K)) := by sorry
