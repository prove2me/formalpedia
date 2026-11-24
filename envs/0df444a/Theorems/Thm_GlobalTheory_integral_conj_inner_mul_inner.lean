-- Prove2me | Theorems.Thm_GlobalTheory_integral_conj_inner_mul_inner
-- name    : GlobalTheory.integral_conj_inner_mul_inner
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:55:48.390902+00:00
-- url     : https://prove2.me/theorems/ebee2376-5f10-4182-97f9-fd30ee059de0
-- title:
--   Global Theory: integral conj inner mul inner
-- statement:
--   The Global Theory construction uses the integral conj inner mul inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IntegralConjInnerMulInnerOfIsEmptyEquiv.lean#L153-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IntegralConjInnerMulInnerOfIsEmptyEquiv.lean#L153-L179

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegralConjInnerMulInnerOfIsEmptyEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure
open scoped InnerProductSpace ComplexConjugate
open GlobalTheory
variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
  {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]
  (ρ : Representation ℂ K V) (σ : Representation ℂ K W)

theorem GlobalTheory.integral_conj_inner_mul_inner [ρ.IsIrreducible] (hρc : ∀ v, Continuous fun k => ρ k v)
    (hρu : ∀ k v, ‖ρ k v‖ = ‖v‖) (u v u' v' : V) :
    ∫ k, conj ⟪u, ρ k v⟫_ℂ * ⟪u', ρ k v'⟫_ℂ ∂μ =
      ⟪u', u⟫_ℂ * ⟪v, v'⟫_ℂ / (Module.finrank ℂ V : ℂ) := by sorry
