-- Prove2me | Theorems.Thm_GlobalTheory_exists_circle_ne_zero_of_frequently_ne_zero
-- name    : GlobalTheory.exists_circle_ne_zero_of_frequently_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:13:39.655334+00:00
-- url     : https://prove2.me/theorems/d77525ad-5587-4035-b723-d59739c4e868
-- title:
--   Global Theory: exists circle ne zero of frequently ne zero
-- statement:
--   The Global Theory construction uses the exists circle ne zero of frequently ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DifferentiableOnQuotientOfDifferentiableOnSlice.lean#L9-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/DifferentiableOnQuotientOfDifferentiableOnSlice.lean#L9-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DifferentiableOnQuotientOfDifferentiableOnSlice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Metric Set
open scoped Topology
open GlobalTheory

theorem GlobalTheory.exists_circle_ne_zero_of_frequently_ne_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {S : Set E} {g : E → ℂ} {z₀ : E} (hS : S ∈ 𝓝 z₀)
    (hg : DifferentiableOn ℂ g S) (hfr : ∃ᶠ z in 𝓝 z₀, g z ≠ 0) :
    ∃ (v : E) (r : ℝ), 0 < r ∧ (∀ t ∈ closedBall (0 : ℂ) r, z₀ + t • v ∈ S) ∧
      ∀ t ∈ sphere (0 : ℂ) r, g (z₀ + t • v) ≠ 0 := by sorry
