-- Prove2me | Theorems.Thm_GlobalTheory_PeriodChart_isHermitian_iff
-- name    : GlobalTheory.PeriodChart.isHermitian_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:40:41.54826+00:00
-- url     : https://prove2.me/theorems/1a3653f0-45cf-49ae-8d68-79695c333aca
-- title:
--   Period Chart: is Hermitian iff
-- statement:
--   The Period Chart construction uses the is Hermitian iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L253-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L253-L271

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsContraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodChart
variable {g : ℕ}

theorem GlobalTheory.PeriodChart.isHermitian_iff (G : Matrix (Fin g) (Fin g) ℂ) :
    G.IsHermitian ↔ ∀ z w, sesq G z w = starRingEnd ℂ (sesq G w z) := by sorry
