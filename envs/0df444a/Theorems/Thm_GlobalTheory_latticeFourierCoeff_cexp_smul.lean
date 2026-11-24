-- Prove2me | Theorems.Thm_GlobalTheory_latticeFourierCoeff_cexp_smul
-- name    : GlobalTheory.latticeFourierCoeff_cexp_smul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:02:23.931297+00:00
-- url     : https://prove2.me/theorems/fe92d03b-cf4e-4809-8050-7cceb41aa0ec
-- title:
--   Global Theory: lattice Fourier Coeff cexp smul
-- statement:
--   The Global Theory construction uses the lattice Fourier Coeff cexp smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LatticeFourierOfContDiffFiniteDimensional.lean#L226-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LatticeFourierOfContDiffFiniteDimensional.lean#L226-L245

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

theorem GlobalTheory.latticeFourierCoeff_cexp_smul [CompleteSpace V] [DecidableEq E] {μ ν : E} (hμ : μ ∈ L*)
    (hν : ν ∈ L*) (v : V) :
    latticeFourierCoeff L (fun b ↦ e[⟪μ, b⟫] • v) ν = if μ = ν then v else 0 := by sorry
