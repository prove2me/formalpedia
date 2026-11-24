-- Prove2me | Theorems.Thm_GlobalTheory_OnePoint_isIntegrallyClosedIn_fractionField_powerSeries
-- name    : GlobalTheory.OnePoint.isIntegrallyClosedIn_fractionField_powerSeries
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:37:47.986561+00:00
-- url     : https://prove2.me/theorems/74f345ed-289f-4abe-89b5-3bba0c12df42
-- title:
--   One Point: is Integrally Closed In fraction Field power Series
-- statement:
--   The One Point construction uses the is Integrally Closed In fraction Field power Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegrallyClosedInFractionFieldPowerSeries.lean#L85-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegrallyClosedInFractionFieldPowerSeries.lean#L85-L90

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

theorem GlobalTheory.OnePoint.isIntegrallyClosedIn_fractionField_powerSeries (L : Type w) [Field L] [Algebra K⟦X⟧ L]
    [IsFractionRing K⟦X⟧ L] [Algebra K L] [IsScalarTower K K⟦X⟧ L] :
    IsIntegrallyClosedIn K L := by sorry
