-- Prove2me | Theorems.Thm_GlobalTheory_PeriodChart_isUnit_det_of_ker
-- name    : GlobalTheory.PeriodChart.isUnit_det_of_ker
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:40:47.478998+00:00
-- url     : https://prove2.me/theorems/135e1806-d6f9-4f33-bb84-938fb9f6eadb
-- title:
--   Period Chart: is Unit det of ker
-- statement:
--   The Period Chart construction uses the is Unit det of ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L313-L317
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L313-L317

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

theorem GlobalTheory.PeriodChart.isUnit_det_of_ker (M : Matrix (Fin g) (Fin g) ℂ) (h : ∀ z, z ≠ 0 → M *ᵥ z ≠ 0) : IsUnit M.det := by sorry
