-- Prove2me | Theorems.Thm_GlobalTheory_OnePoint_algebraMap_laurentSeries
-- name    : GlobalTheory.OnePoint.algebraMap_laurentSeries
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:05:04.82227+00:00
-- url     : https://prove2.me/theorems/db9752af-0197-468c-a565-48acb7f415ad
-- title:
--   One Point: algebra Map laurent Series
-- statement:
--   The One Point construction uses the algebra Map laurent Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegrallyClosedInFractionFieldPowerSeries.lean#L92-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegrallyClosedInFractionFieldPowerSeries.lean#L92-L94

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

theorem GlobalTheory.OnePoint.algebraMap_laurentSeries : algebraMap K K⸨X⸩ = HahnSeries.C := by sorry
