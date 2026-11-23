-- Prove2me | Theorems.Thm_GlobalTheory_exists_equiv_innerDual
-- name    : GlobalTheory.exists_equiv_innerDual
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:51:25.68099+00:00
-- url     : https://prove2.me/theorems/6610e5ba-40be-4493-8359-4fabf5b6f3a9
-- title:
--   Global Theory: exists equiv inner Dual
-- statement:
--   The Global Theory construction uses the exists equiv inner Dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LatticeFourierOfContDiffFiniteDimensional.lean#L309-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LatticeFourierOfContDiffFiniteDimensional.lean#L309-L324

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
variable (L)

theorem GlobalTheory.exists_equiv_innerDual {ι : Type*} [Fintype ι] (b : Basis ι ℤ L) :
    ∃ b' : Basis ι ℝ E, L* = Submodule.span ℤ (range b') ∧ ∃ φ : (ι → ℤ) ≃ L*,
      ∀ n x, ⟪(φ n : E), (b.ofZLatticeBasis ℝ L).equivFun.symm x⟫ = ∑ i, n i * x i := by sorry
