-- Prove2me | Theorems.Thm_GlobalTheory_T_smooth_of_limit_class_stable_under_directional_derivs
-- name    : GlobalTheory.T.smooth_of_limit_class_stable_under_directional_derivs
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:38:19.53765+00:00
-- url     : https://prove2.me/theorems/25cf3520-cff8-4e43-bd04-7f7441e742ae
-- title:
--   T: smooth of limit class stable under directional derivs
-- statement:
--   The T construction uses the smooth of limit class stable under directional derivs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SmoothOfLimitClassStableUnderDirectionalDerivsStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SmoothOfLimitClassStableUnderDirectionalDerivsStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SmoothOfLimitClassStableUnderDirectionalDerivs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_DifferentiableAtLimitOfDirectionalDerivsConvergeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SmoothOfLimitClassStableUnderDirectionalDerivsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.smooth_of_limit_class_stable_under_directional_derivs : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {A : Type} [Fintype A] (v : A → E) (c : A → E →L[ℝ] ℝ), (∀ x, ∑ a, c a x • v a = x) → ∀ P : (E → ℂ) → Prop, (∀ φ, P φ → ∃ g : ℕ → E → ℂ, (∀ j, Differentiable ℝ (g j)) ∧ TendstoLocallyUniformly g φ Filter.atTop ∧ ∀ a, ∃ α : E → ℂ, ContDiff ℝ ∞ α ∧ ∃ χ, P χ ∧ TendstoLocallyUniformly (fun j y => fderiv ℝ (g j) y (v a)) (fun y => α y * φ y + χ y) Filter.atTop) → ∀ φ, P φ → ContDiff ℝ ∞ φ := by sorry
