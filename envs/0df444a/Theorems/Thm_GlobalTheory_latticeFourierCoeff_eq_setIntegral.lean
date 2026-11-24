-- Prove2me | Theorems.Thm_GlobalTheory_latticeFourierCoeff_eq_setIntegral
-- name    : GlobalTheory.latticeFourierCoeff_eq_setIntegral
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:02:11.967653+00:00
-- url     : https://prove2.me/theorems/58189c35-b89e-4b1c-8444-b7731ebea482
-- title:
--   Global Theory: lattice Fourier Coeff eq set Integral
-- statement:
--   The Global Theory construction uses the lattice Fourier Coeff eq set Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LatticeFourierOfContDiffFiniteDimensional.lean#L89-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LatticeFourierOfContDiffFiniteDimensional.lean#L89-L100

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

theorem GlobalTheory.latticeFourierCoeff_eq_setIntegral {A : E → V} (hA : ∀ x ∈ L, Function.Periodic A x)
    {ν : E} (hν : ν ∈ L*) {F : Set E} (hF : IsAddFundamentalDomain L F volume) :
    latticeFourierCoeff L A ν =
      (ZLattice.covolume L)⁻¹ • ∫ b in F, e[-⟪ν, b⟫] • A b := by sorry
