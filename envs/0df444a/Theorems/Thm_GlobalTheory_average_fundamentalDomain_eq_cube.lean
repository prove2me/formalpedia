-- Prove2me | Theorems.Thm_GlobalTheory_average_fundamentalDomain_eq_cube
-- name    : GlobalTheory.average_fundamentalDomain_eq_cube
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:50:36.899354+00:00
-- url     : https://prove2.me/theorems/ef2cfe09-5b9a-4f22-829b-0df9bb51634a
-- title:
--   Global Theory: average fundamental Domain eq cube
-- statement:
--   The Global Theory construction uses the average fundamental Domain eq cube property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LatticeFourierOfContDiffFiniteDimensional.lean#L262-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LatticeFourierOfContDiffFiniteDimensional.lean#L262-L290

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
omit [InnerProductSpace ℝ E]

theorem GlobalTheory.average_fundamentalDomain_eq_cube [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] (b : Basis ι ℝ E) (μ : Measure E) [μ.IsAddHaarMeasure] (g : E → V) :
    (μ.real (ZSpan.fundamentalDomain b))⁻¹ • ∫ y in ZSpan.fundamentalDomain b, g y ∂μ =
      ∫ x in {x : ι → ℝ | ∀ i, x i ∈ Ioc (0 : ℝ) 1}, g (b.equivFun.symm x) := by sorry
