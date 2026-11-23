-- Prove2me | Theorems.Thm_GlobalTheory_OnePoint_isIntegrallyClosedIn_fractionField_of_residue
-- name    : GlobalTheory.OnePoint.isIntegrallyClosedIn_fractionField_of_residue
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:05:35.509723+00:00
-- url     : https://prove2.me/theorems/4cf6ff97-26b7-459d-886d-2fba780e81fd
-- title:
--   One Point: is Integrally Closed In fraction Field of residue
-- statement:
--   The One Point construction uses the is Integrally Closed In fraction Field of residue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegrallyClosedInFractionFieldPowerSeries.lean#L55-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegrallyClosedInFractionFieldPowerSeries.lean#L55-L71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsIntegrallyClosedInFractionFieldPowerSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped LaurentSeries PowerSeries
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.OnePoint
universe u v w
variable {K : Type u} [Field K]

theorem GlobalTheory.OnePoint.isIntegrallyClosedIn_fractionField_of_residue (R : Type v) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [Algebra K R] (L : Type w) [Field L] [Algebra R L]
    [IsFractionRing R L] [Algebra K L] [IsScalarTower K R L]
    (hres : ∀ r : R, ∃ c : K, ¬ IsUnit (r - algebraMap K R c)) : IsIntegrallyClosedIn K L := by sorry
