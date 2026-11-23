-- Prove2me | Theorems.Thm_GlobalTheory_exists_bound_of_lattice_periodic
-- name    : GlobalTheory.exists_bound_of_lattice_periodic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:51:13.916271+00:00
-- url     : https://prove2.me/theorems/66c04c6f-d94b-4e75-ba3b-1bab35482c47
-- title:
--   Global Theory: exists bound of lattice periodic
-- statement:
--   The Global Theory construction uses the exists bound of lattice periodic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LatticeFourierOfContDiffFiniteDimensional.lean#L195-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LatticeFourierOfContDiffFiniteDimensional.lean#L195-L204

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
omit [MeasurableSpace E] [BorelSpace E]

theorem GlobalTheory.exists_bound_of_lattice_periodic {W : Type*} [NormedAddCommGroup W] {f : E → W}
    (hf : ∀ x ∈ L, Function.Periodic f x) (hc : Continuous f) : ∃ M, ∀ b, ‖f b‖ ≤ M := by sorry
