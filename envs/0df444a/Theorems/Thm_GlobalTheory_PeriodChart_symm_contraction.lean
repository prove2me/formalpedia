-- Prove2me | Theorems.Thm_GlobalTheory_PeriodChart_symm_contraction
-- name    : GlobalTheory.PeriodChart.symm_contraction
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:42:55.891186+00:00
-- url     : https://prove2.me/theorems/b13d074e-0e0a-444c-b885-4cf4d8998ee5
-- title:
--   Period Chart: symm contraction
-- statement:
--   The Period Chart construction uses the symm contraction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L13-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L13-L76

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
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.PeriodChart.symm_contraction (F F₀ : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (N : V →ₗ⋆[ℂ] V)
    (hF : ∀ z w, F z w = starRingEnd ℂ (F w z))
    (hp : ∀ z, z ≠ 0 → 0 < (F z z).re) (hp₀ : ∀ z, z ≠ 0 → 0 < (F₀ z z).re)
    (h : ∀ z w, (F (z + N z) (w + N w)).im = (F₀ z w).im) :
    (∀ z w, F₀ (N z) w = F₀ (N w) z) ∧ ∀ z, z ≠ 0 → (F₀ (N z) (N z)).re < (F₀ z z).re := by sorry
