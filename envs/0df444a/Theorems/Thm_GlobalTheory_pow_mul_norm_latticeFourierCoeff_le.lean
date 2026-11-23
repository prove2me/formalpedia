-- Prove2me | Theorems.Thm_GlobalTheory_pow_mul_norm_latticeFourierCoeff_le
-- name    : GlobalTheory.pow_mul_norm_latticeFourierCoeff_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:38.563796+00:00
-- url     : https://prove2.me/theorems/8b19818b-08bb-4750-a068-b66979af0dbd
-- title:
--   Global Theory: pow mul norm lattice Fourier Coeff le
-- statement:
--   The Global Theory construction uses the pow mul norm lattice Fourier Coeff le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LatticeFourierOfContDiffFiniteDimensional.lean#L206-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LatticeFourierOfContDiffFiniteDimensional.lean#L206-L224

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

theorem GlobalTheory.pow_mul_norm_latticeFourierCoeff_le {A : E → V} (hA : ∀ x ∈ L, Function.Periodic A x)
    {k : ℕ} (hk : ContDiff ℝ k A) {M : ℝ} (hM : ∀ x, ‖iteratedFDeriv ℝ k A x‖ ≤ M)
    {ν : E} (hν : ν ∈ L*) :
    (4 * ‖ν‖) ^ k * ‖latticeFourierCoeff L A ν‖ ≤ M := by sorry
