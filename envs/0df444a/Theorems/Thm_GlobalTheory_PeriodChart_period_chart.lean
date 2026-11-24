-- Prove2me | Theorems.Thm_GlobalTheory_PeriodChart_period_chart
-- name    : GlobalTheory.PeriodChart.period_chart
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:42:30.991535+00:00
-- url     : https://prove2.me/theorems/ac609334-8671-40cc-ae6e-80e87f8e93a3
-- title:
--   Period Chart: period chart
-- statement:
--   The Period Chart construction uses the period chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L931-L1053
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L931-L1053

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

theorem GlobalTheory.PeriodChart.period_chart : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty → ∀ P₀, IsPeriod D ty P₀ → ∃ (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D.La →+ (Fin g → ℂ))), 2 * m = Module.finrank ℚ E * D.p * D.q ∧ IsOpen B ∧ Convex ℝ B ∧ 0 ∈ B ∧ P 0 = P₀ ∧ IsHolPeriods D ty B P ∧ ∀ P', IsPeriod D ty P' → ∃! b, b ∈ B ∧ ∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ a, P' a = h (P b a)) := by sorry
