-- Prove2me | Theorems.Thm_GlobalTheory_hasSum_latticeFourier_of_summable_norm
-- name    : GlobalTheory.hasSum_latticeFourier_of_summable_norm
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:35:10.335803+00:00
-- url     : https://prove2.me/theorems/5de374b4-847f-4ce6-ab20-26710943f28a
-- title:
--   Global Theory: has Sum lattice Fourier of summable norm
-- statement:
--   The Global Theory construction uses the has Sum lattice Fourier of summable norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LatticeFourierOfContDiffFiniteDimensional.lean#L402-L414
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LatticeFourierOfContDiffFiniteDimensional.lean#L402-L414

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

theorem GlobalTheory.hasSum_latticeFourier_of_summable_norm [CompleteSpace V] {A : E → V}
    (hA : ∀ x ∈ L, Function.Periodic A x) (hc : Continuous A)
    (hs : Summable fun ν : L* ↦ ‖latticeFourierCoeff L A ν‖) (y : E) :
    HasSum (fun ν : L* ↦ e[⟪(ν : E), y⟫] • latticeFourierCoeff L A ν) (A y) := by sorry
