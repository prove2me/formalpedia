-- Prove2me | Theorems.Thm_GlobalTheory_latticeFourierCoeff_eq_setIntegral_haar
-- name    : GlobalTheory.latticeFourierCoeff_eq_setIntegral_haar
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:48:14.037864+00:00
-- url     : https://prove2.me/theorems/54b1ca90-9f39-5ddb-932f-0038471b1654
-- title:
--   Global Theory: lattice Fourier Coeff eq set Integral haar
-- statement:
--   The Global Theory construction uses the lattice Fourier Coeff eq set Integral haar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LatticeFourierOfContDiffFiniteDimensional.lean#L292-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LatticeFourierOfContDiffFiniteDimensional.lean#L292-L304

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

theorem GlobalTheory.latticeFourierCoeff_eq_setIntegral_haar {A : E → V} (hA : ∀ x ∈ L, Function.Periodic A x)
    {ν : E} (hν : ν ∈ L*) (μ : Measure E) [μ.IsAddHaarMeasure] {F : Set E}
    (hF : IsAddFundamentalDomain L F μ) :
    latticeFourierCoeff L A ν = (ZLattice.covolume L μ)⁻¹ • ∫ b in F, e[-⟪ν, b⟫] • A b ∂μ := by sorry
