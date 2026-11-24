-- Prove2me | Theorems.Thm_GlobalTheory_PeriodChart_exists_anti
-- name    : GlobalTheory.PeriodChart.exists_anti
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:43:16.965042+00:00
-- url     : https://prove2.me/theorems/4e2ed3ef-0fdf-4f14-8602-48befb73f41c
-- title:
--   Period Chart: exists anti
-- statement:
--   The Period Chart construction uses the exists anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L273-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L273-L283

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

theorem GlobalTheory.PeriodChart.exists_anti (N : (Fin g → ℂ) →ₗ⋆[ℂ] (Fin g → ℂ)) : ∃ Z, N = anti Z := by sorry
