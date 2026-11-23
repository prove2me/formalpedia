-- Prove2me | Theorems.Thm_GlobalTheory_OnePoint_isIntegrallyClosedIn_laurentSeries
-- name    : GlobalTheory.OnePoint.isIntegrallyClosedIn_laurentSeries
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:04:57.786268+00:00
-- url     : https://prove2.me/theorems/187d6420-a3db-4e4d-b531-2986d8348d90
-- title:
--   One Point: is Integrally Closed In laurent Series
-- statement:
--   The One Point construction uses the is Integrally Closed In laurent Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegrallyClosedInFractionFieldPowerSeries.lean#L96-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegrallyClosedInFractionFieldPowerSeries.lean#L96-L98

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

theorem GlobalTheory.OnePoint.isIntegrallyClosedIn_laurentSeries : IsIntegrallyClosedIn K K⸨X⸩ := by sorry
