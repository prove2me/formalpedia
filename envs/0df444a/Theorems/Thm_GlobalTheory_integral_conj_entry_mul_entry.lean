-- Prove2me | Theorems.Thm_GlobalTheory_integral_conj_entry_mul_entry
-- name    : GlobalTheory.integral_conj_entry_mul_entry
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:55:50.978776+00:00
-- url     : https://prove2.me/theorems/162cb569-78c7-4dcb-963f-f40852a7d306
-- title:
--   Global Theory: integral conj entry mul entry
-- statement:
--   The Global Theory construction uses the integral conj entry mul entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IntegralConjInnerMulInnerOfIsEmptyEquiv.lean#L181-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/IntegralConjInnerMulInnerOfIsEmptyEquiv.lean#L181-L188

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

theorem GlobalTheory.integral_conj_entry_mul_entry [ρ.IsIrreducible] (hρc : ∀ v, Continuous fun k => ρ k v)
    (hρu : ∀ k v, ‖ρ k v‖ = ‖v‖) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ V) (i j i' j' : ι) :
    ∫ k, conj ⟪b i, ρ k (b j)⟫_ℂ * ⟪b i', ρ k (b j')⟫_ℂ ∂μ =
      if i = i' ∧ j = j' then (Module.finrank ℂ V : ℂ)⁻¹ else 0 := by sorry
