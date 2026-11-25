-- Prove2me | Theorems.Thm_GlobalTheory_latticeFourier_of_contDiff_finiteDimensional
-- name    : GlobalTheory.latticeFourier_of_contDiff_finiteDimensional
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:48:39.326534+00:00
-- url     : https://prove2.me/theorems/9cf8cc59-a188-4549-8e70-7ddb5b0830d7
-- title:
--   Global Theory: lattice Fourier of cont Diff finite Dimensional
-- statement:
--   The Global Theory construction uses the lattice Fourier of cont Diff finite Dimensional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LatticeFourierOfContDiffFiniteDimensional.lean#L439-L447
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LatticeFourierOfContDiffFiniteDimensional.lean#L439-L447

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

theorem GlobalTheory.latticeFourier_of_contDiff_finiteDimensional [FiniteDimensional ℂ V] {A : E → V}
    (hsm : ContDiff ℝ ∞ A) (hA : ∀ x ∈ L, Function.Periodic A x) :
    (BddAbove (range fun b ↦ ‖A b‖) ∧ ∀ ν : L*, ‖latticeFourierCoeff L A ν‖ ≤ ⨆ b, ‖A b‖) ∧
    (Summable fun ν : L* ↦ ‖latticeFourierCoeff L A ν‖) ∧
    (∀ b, HasSum (fun ν : L* ↦ e[⟪(ν : E), b⟫] • latticeFourierCoeff L A ν) (A b)) ∧
    ∀ (c : E) (ν : L*), latticeFourierCoeff L (fun b ↦ A (b + c)) ν =
      e[⟪(ν : E), c⟫] • latticeFourierCoeff L A ν := by sorry
