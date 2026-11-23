-- Prove2me | Theorems.Thm_GlobalTheory_PeriodChart_sesq_apply
-- name    : GlobalTheory.PeriodChart.sesq_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:25:55.362657+00:00
-- url     : https://prove2.me/theorems/8f3804ee-6e33-4201-84b2-ec24b162887c
-- title:
--   Period Chart: sesq apply
-- statement:
--   The Period Chart construction uses the sesq apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L220-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L220-L220

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

theorem GlobalTheory.PeriodChart.sesq_apply (G : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) : sesq G z w = hermForm G z w := by sorry
