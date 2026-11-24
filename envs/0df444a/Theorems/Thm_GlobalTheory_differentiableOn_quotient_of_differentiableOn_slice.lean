-- Prove2me | Theorems.Thm_GlobalTheory_differentiableOn_quotient_of_differentiableOn_slice
-- name    : GlobalTheory.differentiableOn_quotient_of_differentiableOn_slice
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:58:30.309374+00:00
-- url     : https://prove2.me/theorems/0abc9a3b-470b-478c-905e-9a51263fb365
-- title:
--   Global Theory: differentiable On quotient of differentiable On slice
-- statement:
--   The Global Theory construction uses the differentiable On quotient of differentiable On slice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DifferentiableOnQuotientOfDifferentiableOnSlice.lean#L40-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DifferentiableOnQuotientOfDifferentiableOnSlice.lean#L40-L100

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DifferentiableOnQuotientOfDifferentiableOnSlice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Metric Set
open scoped Topology
open GlobalTheory

theorem GlobalTheory.differentiableOn_quotient_of_differentiableOn_slice :
    ∀ (V V' : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
      [NormedAddCommGroup V'] [NormedSpace ℂ V'] [FiniteDimensional ℂ V'] (W : Set (V × V'))
      (f θ F : V × V' → ℂ), IsOpen W → DifferentiableOn ℂ f W → DifferentiableOn ℂ θ W →
      (∀ w ∈ W, F w * θ w = f w) →
      (∀ b, DifferentiableOn ℂ (fun z => F (b, z)) {z | (b, z) ∈ W}) →
      (∀ w ∈ W, ∃ᶠ z in nhds w.2, θ (w.1, z) ≠ 0) → DifferentiableOn ℂ F W := by sorry
