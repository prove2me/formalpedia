-- Prove2me | Theorems.Thm_GlobalTheory_inner_rankOneAverage
-- name    : GlobalTheory.inner_rankOneAverage
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:56:21.519067+00:00
-- url     : https://prove2.me/theorems/4a6a199a-9910-4700-9426-7046dca46bd2
-- title:
--   Global Theory: inner rank One Average
-- statement:
--   The Global Theory construction uses the inner rank One Average property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IntegralConjInnerMulInnerOfIsEmptyEquiv.lean#L121-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IntegralConjInnerMulInnerOfIsEmptyEquiv.lean#L121-L129

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
variable [IsFiniteMeasure μ] [μ.IsMulLeftInvariant]
  (ρ : Representation ℂ K V) (σ : Representation ℂ K W)
omit [FiniteDimensional ℂ V]

theorem GlobalTheory.inner_rankOneAverage (hρc : ∀ v, Continuous fun k => ρ k v)
    (hρu : ∀ k v, ‖ρ k v‖ = ‖v‖) (hσc : ∀ w, Continuous fun k => σ k w) (u v : V) (u' w : W) :
    ⟪u', rankOneAverage μ ρ σ hρc hρu hσc v w u⟫_ℂ =
      ∫ k, conj ⟪u, ρ k v⟫_ℂ * ⟪u', σ k w⟫_ℂ ∂μ := by sorry
