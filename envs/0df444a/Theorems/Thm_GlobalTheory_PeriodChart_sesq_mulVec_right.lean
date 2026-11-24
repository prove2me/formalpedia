-- Prove2me | Theorems.Thm_GlobalTheory_PeriodChart_sesq_mulVec_right
-- name    : GlobalTheory.PeriodChart.sesq_mulVec_right
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:42:23.006245+00:00
-- url     : https://prove2.me/theorems/01abbd1b-ea8e-47b3-bbb5-b1e7bc19f1b7
-- title:
--   Period Chart: sesq mul Vec right
-- statement:
--   The Period Chart construction uses the sesq mul Vec right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L249-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L249-L251

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

theorem GlobalTheory.PeriodChart.sesq_mulVec_right (G A : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    sesq G z (A *ᵥ w) = sesq (G * A.map (starRingEnd ℂ)) z w := by sorry
