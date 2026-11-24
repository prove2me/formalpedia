-- Prove2me | Theorems.Thm_GlobalTheory_norm_fwdDiff_iter_le
-- name    : GlobalTheory.norm_fwdDiff_iter_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:13:17.966583+00:00
-- url     : https://prove2.me/theorems/205e9fe5-2cf3-4420-9d62-8d968f3836e9
-- title:
--   Global Theory: norm fwd Diff iter le
-- statement:
--   The Global Theory construction uses the norm fwd Diff iter le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LatticeFourierOfContDiffFiniteDimensional.lean#L175-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LatticeFourierOfContDiffFiniteDimensional.lean#L175-L191

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

theorem GlobalTheory.norm_fwdDiff_iter_le (c : E) (k : ℕ) {A : E → V} (hA : ContDiff ℝ k A) {M : ℝ}
    (hM : ∀ x, ‖iteratedFDeriv ℝ k A x‖ ≤ M) (x : E) :
    ‖(fwdDiff c)^[k] A x‖ ≤ ‖c‖ ^ k * M := by sorry
