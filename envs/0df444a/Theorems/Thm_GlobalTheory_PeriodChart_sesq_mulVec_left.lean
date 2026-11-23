-- Prove2me | Theorems.Thm_GlobalTheory_PeriodChart_sesq_mulVec_left
-- name    : GlobalTheory.PeriodChart.sesq_mulVec_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:24:21.266039+00:00
-- url     : https://prove2.me/theorems/e21fefbc-a0d6-4569-88bc-332b982cbc20
-- title:
--   Period Chart: sesq mul Vec left
-- statement:
--   The Period Chart construction uses the sesq mul Vec left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L245-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L245-L247

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

theorem GlobalTheory.PeriodChart.sesq_mulVec_left (G A : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    sesq G (A *ᵥ z) w = sesq (Aᵀ * G) z w := by sorry
