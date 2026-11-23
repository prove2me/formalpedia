-- Prove2me | Theorems.Thm_GlobalTheory_PeriodChart_star_single
-- name    : GlobalTheory.PeriodChart.star_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:24:36.802655+00:00
-- url     : https://prove2.me/theorems/298ab2a4-aa0d-4d28-ba92-c01335f25a0c
-- title:
--   Period Chart: star single
-- statement:
--   The Period Chart construction uses the star single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L229-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L229-L233

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

theorem GlobalTheory.PeriodChart.star_single (k : Fin g) : star (Pi.single k (1 : ℂ) : Fin g → ℂ) = Pi.single k 1 := by sorry
