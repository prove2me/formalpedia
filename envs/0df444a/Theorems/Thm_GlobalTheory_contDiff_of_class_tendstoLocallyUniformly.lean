-- Prove2me | Theorems.Thm_GlobalTheory_contDiff_of_class_tendstoLocallyUniformly
-- name    : GlobalTheory.contDiff_of_class_tendstoLocallyUniformly
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:14:54.713079+00:00
-- url     : https://prove2.me/theorems/0f39b719-2480-4bc7-a1b7-81a63e55078d
-- title:
--   Global Theory: cont Diff of class tendsto Locally Uniformly
-- statement:
--   The Global Theory construction uses the cont Diff of class tendsto Locally Uniformly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SmoothOfLimitClassStableUnderDirectionalDerivs.lean#L7-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SmoothOfLimitClassStableUnderDirectionalDerivs.lean#L7-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_DifferentiableAtLimitOfDirectionalDerivsConvergeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SmoothOfLimitClassStableUnderDirectionalDerivs
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

theorem GlobalTheory.contDiff_of_class_tendstoLocallyUniformly : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {A : Type} [Fintype A] (v : A → E) (c : A → E →L[ℝ] ℝ), (∀ x, ∑ a, c a x • v a = x) → ∀ P : (E → ℂ) → Prop, (∀ φ, P φ → ∃ g : ℕ → E → ℂ, (∀ j, Differentiable ℝ (g j)) ∧ TendstoLocallyUniformly g φ Filter.atTop ∧ ∀ a, ∃ α : E → ℂ, ContDiff ℝ ∞ α ∧ ∃ χ, P χ ∧ TendstoLocallyUniformly (fun j y => fderiv ℝ (g j) y (v a)) (fun y => α y * φ y + χ y) Filter.atTop) → ∀ φ, P φ → ContDiff ℝ ∞ φ := by sorry
