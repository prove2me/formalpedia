-- Prove2me | Theorems.Thm_GlobalTheory_summable_norm_inv_pow_innerDual
-- name    : GlobalTheory.summable_norm_inv_pow_innerDual
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:22:36.518066+00:00
-- url     : https://prove2.me/theorems/e08d09d3-0fd9-4031-808a-1be08e592259
-- title:
--   Global Theory: summable norm inv pow inner Dual
-- statement:
--   The Global Theory construction uses the summable norm inv pow inner Dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LatticeFourierOfContDiffFiniteDimensional.lean#L327-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LatticeFourierOfContDiffFiniteDimensional.lean#L327-L332

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

theorem GlobalTheory.summable_norm_inv_pow_innerDual {k : ℕ} (hk : finrank ℝ E < k) :
    Summable fun ν : L* ↦ ‖(ν : E)‖⁻¹ ^ k := by sorry
