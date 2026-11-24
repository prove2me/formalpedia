-- Prove2me | Theorems.Thm_GlobalTheory_latticeFourierCoeff_clm
-- name    : GlobalTheory.latticeFourierCoeff_clm
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:02:14.241266+00:00
-- url     : https://prove2.me/theorems/c2a50074-3543-4e7d-b699-e212614dbacf
-- title:
--   Global Theory: lattice Fourier Coeff clm
-- statement:
--   The Global Theory construction uses the lattice Fourier Coeff clm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LatticeFourierOfContDiffFiniteDimensional.lean#L150-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LatticeFourierOfContDiffFiniteDimensional.lean#L150-L155

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

theorem GlobalTheory.latticeFourierCoeff_clm [CompleteSpace V] {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℂ W] [CompleteSpace W] (T : V →L[ℂ] W) {A : E → V} (hA : Continuous A) (ν : E) :
    latticeFourierCoeff L (fun b ↦ T (A b)) ν = T (latticeFourierCoeff L A ν) := by sorry
