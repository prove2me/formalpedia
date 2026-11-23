-- Prove2me | Theorems.Thm_GlobalTheory_PeriodChart_anti_apply
-- name    : GlobalTheory.PeriodChart.anti_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:24:54.954197+00:00
-- url     : https://prove2.me/theorems/f87fc60d-e3c0-4a1e-acef-304e2ce9921c
-- title:
--   Period Chart: anti apply
-- statement:
--   The Period Chart construction uses the anti apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L227-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L227-L227

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

theorem GlobalTheory.PeriodChart.anti_apply (Z : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) : anti Z z = Z *ᵥ star z := by sorry
