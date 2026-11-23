-- Prove2me | Theorems.Thm_GlobalTheory_continuous_cexp_neg_inner_smul
-- name    : GlobalTheory.continuous_cexp_neg_inner_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:35:20.11269+00:00
-- url     : https://prove2.me/theorems/8d5fd827-0526-4f6b-8224-51befa1755ee
-- title:
--   Global Theory: continuous cexp neg inner smul
-- statement:
--   The Global Theory construction uses the continuous cexp neg inner smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LatticeFourierOfContDiffFiniteDimensional.lean#L85-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LatticeFourierOfContDiffFiniteDimensional.lean#L85-L87

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
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem GlobalTheory.continuous_cexp_neg_inner_smul {A : E → V} (hA : Continuous A) (ν : E) :
    Continuous fun b : E ↦ e[-⟪ν, b⟫] • A b := by sorry
