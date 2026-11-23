-- Prove2me | Theorems.Thm_GlobalTheory_OnePoint_exists_eq_C_of_isAlgebraic
-- name    : GlobalTheory.OnePoint.exists_eq_C_of_isAlgebraic
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:05:27.505999+00:00
-- url     : https://prove2.me/theorems/7c9e840f-7a71-4400-b294-db266c441e1f
-- title:
--   One Point: exists eq C of is Algebraic
-- statement:
--   The One Point construction uses the exists eq C of is Algebraic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegrallyClosedInFractionFieldPowerSeries.lean#L100-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegrallyClosedInFractionFieldPowerSeries.lean#L100-L104

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

theorem GlobalTheory.OnePoint.exists_eq_C_of_isAlgebraic {x : K⸨X⸩} (hx : IsAlgebraic K x) :
    ∃ c : K, x = HahnSeries.C c := by sorry
