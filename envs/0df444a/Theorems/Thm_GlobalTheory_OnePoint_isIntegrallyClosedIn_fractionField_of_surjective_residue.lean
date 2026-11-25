-- Prove2me | Theorems.Thm_GlobalTheory_OnePoint_isIntegrallyClosedIn_fractionField_of_surjective_residue
-- name    : GlobalTheory.OnePoint.isIntegrallyClosedIn_fractionField_of_surjective_residue
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:15:17.203281+00:00
-- url     : https://prove2.me/theorems/2dba756e-f13c-43c0-b4a7-ac876cb8a787
-- title:
--   One Point: is Integrally Closed In fraction Field of surjective residue
-- statement:
--   The One Point construction uses the is Integrally Closed In fraction Field of surjective residue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegrallyClosedInFractionFieldPowerSeries.lean#L73-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegrallyClosedInFractionFieldPowerSeries.lean#L73-L83

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

theorem GlobalTheory.OnePoint.isIntegrallyClosedIn_fractionField_of_surjective_residue (R : Type v) [CommRing R]
    [IsDomain R] [IsLocalRing R] [IsIntegrallyClosed R] [Algebra K R] (L : Type w) [Field L]
    [Algebra R L] [IsFractionRing R L] [Algebra K L] [IsScalarTower K R L]
    (hres : Function.Surjective fun c : K ↦ IsLocalRing.residue R (algebraMap K R c)) :
    IsIntegrallyClosedIn K L := by sorry
