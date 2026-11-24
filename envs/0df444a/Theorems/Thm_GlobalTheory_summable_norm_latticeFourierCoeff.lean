-- Prove2me | Theorems.Thm_GlobalTheory_summable_norm_latticeFourierCoeff
-- name    : GlobalTheory.summable_norm_latticeFourierCoeff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:22:40.510109+00:00
-- url     : https://prove2.me/theorems/3372bf98-8502-4f3d-930d-4a76e96468a9
-- title:
--   Global Theory: summable norm lattice Fourier Coeff
-- statement:
--   The Global Theory construction uses the summable norm lattice Fourier Coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LatticeFourierOfContDiffFiniteDimensional.lean#L334-L348
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LatticeFourierOfContDiffFiniteDimensional.lean#L334-L348

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

theorem GlobalTheory.summable_norm_latticeFourierCoeff {A : E → V} (hA : ∀ x ∈ L, Function.Periodic A x)
    {k : ℕ} (hk : finrank ℝ E < k) (hAk : ContDiff ℝ k A) :
    Summable fun ν : L* ↦ ‖latticeFourierCoeff L A ν‖ := by sorry
