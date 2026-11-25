-- Prove2me | Theorems.Thm_GlobalTheory_eq_zero_of_latticeFourierCoeff_eq_zero
-- name    : GlobalTheory.eq_zero_of_latticeFourierCoeff_eq_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:44:57.47258+00:00
-- url     : https://prove2.me/theorems/9ad9327c-d79e-5812-8ec2-5dce44de8489
-- title:
--   Global Theory: eq zero of lattice Fourier Coeff eq zero
-- statement:
--   The Global Theory construction uses the eq zero of lattice Fourier Coeff eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LatticeFourierOfContDiffFiniteDimensional.lean#L449-L454
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LatticeFourierOfContDiffFiniteDimensional.lean#L449-L454

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LatticeFourierOfContDiffFiniteDimensional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Set
open scoped RealInnerProductSpace Real Pointwise ContDiff
noncomputable section
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
local notation "e[" t "]" => Complex.exp (2 * (π : ℂ) * Complex.I * ((t : ℝ) : ℂ))
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
local notation "L*" => LinearMap.BilinForm.dualSubmodule (innerₗ E) L
variable {L}

theorem GlobalTheory.eq_zero_of_latticeFourierCoeff_eq_zero [CompleteSpace V] {A : E → V}
    (hA : ∀ x ∈ L, Function.Periodic A x) (hc : Continuous A)
    (h : ∀ ν : L*, latticeFourierCoeff L A ν = 0) (y : E) : A y = 0 := by sorry
