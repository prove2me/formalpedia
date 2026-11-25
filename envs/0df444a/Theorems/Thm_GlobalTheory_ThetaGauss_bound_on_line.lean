-- Prove2me | Theorems.Thm_GlobalTheory_ThetaGauss_bound_on_line
-- name    : GlobalTheory.ThetaGauss.bound_on_line
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:48:36.619198+00:00
-- url     : https://prove2.me/theorems/063529d0-15ec-4f65-9b13-671da97c5189
-- title:
--   Theta Gauss: bound on line
-- statement:
--   The Theta Gauss construction uses the bound on line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DifferentiableFderivApply.lean#L199-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DifferentiableFderivApply.lean#L199-L281

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsImEqLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DifferentiableFderivApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Metric
open scoped ComplexOrder
open GlobalTheory GlobalTheory.ThetaGauss
variable {g : ℕ}

theorem GlobalTheory.ThetaGauss.bound_on_line {θ : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ) (v : Fin g → ℂ)
    (hm : ∀ a, θ a = 0 → fderiv ℂ θ a v = 0) (z w : Fin g → ℂ) (h0 : ∃ s : ℂ, θ (z + s • w) ≠ 0) :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[≠] (0 : ℂ), ‖fderiv ℂ θ (z + s • w) v ^ 2‖ ≤ C * ‖θ (z + s • w)‖ := by sorry
