-- Prove2me | Theorems.Thm_GlobalTheory_Published_Metaplectic_hasTemperateGrowth_eChar
-- name    : GlobalTheory.Published.Metaplectic.hasTemperateGrowth_eChar
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:55.054519+00:00
-- url     : https://prove2.me/theorems/1d07df38-f968-4608-926c-201c06905e05
-- title:
--   Metaplectic: has Temperate Growth e Char
-- statement:
--   The Metaplectic construction uses the has Temperate Growth e Char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/MetaplecticRepresentation.lean#L23-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/MetaplecticRepresentation.lean#L23-L50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix Complex
open scoped Real SchwartzMap ComplexConjugate
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.Metaplectic
variable {ι : Type} [Fintype ι]

theorem GlobalTheory.Published.Metaplectic.hasTemperateGrowth_eChar : Function.HasTemperateGrowth (eChar : ℝ → ℂ) := by sorry
