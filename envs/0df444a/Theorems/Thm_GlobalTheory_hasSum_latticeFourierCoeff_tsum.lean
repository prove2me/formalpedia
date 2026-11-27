-- Prove2me | Theorems.Thm_GlobalTheory_hasSum_latticeFourierCoeff_tsum
-- name    : GlobalTheory.hasSum_latticeFourierCoeff_tsum
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:47:08.840104+00:00
-- url     : https://prove2.me/theorems/6d02e1d8-b0cb-4ea4-a180-d2cea691e282
-- title:
--   Global Theory: has Sum lattice Fourier Coeff tsum
-- statement:
--   The Global Theory construction uses the has Sum lattice Fourier Coeff tsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LatticeFourierOfContDiffFiniteDimensional.lean#L247-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LatticeFourierOfContDiffFiniteDimensional.lean#L247-L258

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

theorem GlobalTheory.hasSum_latticeFourierCoeff_tsum [CompleteSpace V] [DecidableEq E] {ι : Type*}
    [Countable ι] {m : ι → E} (hm : ∀ j, m j ∈ L*) {a : ι → V} (ha : Summable fun j ↦ ‖a j‖)
    {ν : E} (hν : ν ∈ L*) :
    HasSum (fun j ↦ if m j = ν then a j else 0)
      (latticeFourierCoeff L (fun b ↦ ∑' j, e[⟪m j, b⟫] • a j) ν) := by sorry
