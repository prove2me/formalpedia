-- Prove2me | Theorems.Thm_GlobalTheory_differentiableAt_of_tendstoLocallyUniformly_directional
-- name    : GlobalTheory.differentiableAt_of_tendstoLocallyUniformly_directional
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:16:15.408727+00:00
-- url     : https://prove2.me/theorems/b1d18bff-3495-4822-a603-64a9d9b81e5b
-- title:
--   Global Theory: differentiable At of tendsto Locally Uniformly directional
-- statement:
--   The Global Theory construction uses the differentiable At of tendsto Locally Uniformly directional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/DifferentiableAtLimitOfDirectionalDerivsConverge.lean#L31-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/DifferentiableAtLimitOfDirectionalDerivsConverge.lean#L31-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_DifferentiableAtLimitOfDirectionalDerivsConverge
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff Topology
open GlobalTheory
open Filter

theorem GlobalTheory.differentiableAt_of_tendstoLocallyUniformly_directional :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {A : Type} [Fintype A] (v : A → E) (c : A → E →L[ℝ] ℝ), (∀ x, ∑ a, c a x • v a = x) → ∀ (φ : E → ℂ) (g : ℕ → E → ℂ) (ψ : A → E → ℂ), (∀ j, Differentiable ℝ (g j)) → TendstoLocallyUniformly g φ Filter.atTop → (∀ a, TendstoLocallyUniformly (fun j y => fderiv ℝ (g j) y (v a)) (ψ a) Filter.atTop) → ∀ y, DifferentiableAt ℝ φ y ∧ ∀ a, fderiv ℝ φ y (v a) = ψ a y := by sorry
