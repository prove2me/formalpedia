-- Prove2me | Theorems.Thm_GlobalTheory_PerronShift_perron_shift
-- name    : GlobalTheory.PerronShift.perron_shift
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:43:32.538024+00:00
-- url     : https://prove2.me/theorems/165ac6df-68a0-4b01-908c-ca53e7161b07
-- title:
--   Perron Shift: perron shift
-- statement:
--   The Perron Shift construction uses the perron shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/PerronIntegralShiftPrimitiveLFunction.lean#L227-L335
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/PerronIntegralShiftPrimitiveLFunction.lean#L227-L335

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsBoundRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivLFunctionNearZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_AnalyticAtDslope
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PerronIntegralShiftPrimitiveLFunction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.PerronShift
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.PerronShift.perron_shift : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ u T : ℝ, 2 ≤ T → T ≤ u → ∃ T' : ℝ, T ≤ T' ∧ T' ≤ T + 1 ∧ ‖(1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ in (-T')..T', (-(deriv (LFunction χ) (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I) / LFunction χ (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I)) * (u : ℂ) ^ (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I) / (((1 + 1 / Real.log u : ℝ) : ℂ) + t * I))) - (if N = 1 then (u : ℂ) else 0) + ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T' ∧ LFunction χ ρ = 0}, ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤ C * (u * Real.log (N * u * T) ^ 2 / T + Real.log (N * u) + ∑ᶠ ρ ∈ {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 ∧ LFunction χ ρ = 0}, ((analyticOrderNatAt (LFunction χ) ρ : ℕ) : ℝ) / ‖ρ‖) := by sorry
