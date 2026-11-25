-- Prove2me | Theorems.Thm_GlobalTheory_ThetaGauss_eq_exp_of_ode
-- name    : GlobalTheory.ThetaGauss.eq_exp_of_ode
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:47:45.805565+00:00
-- url     : https://prove2.me/theorems/a833b5e1-4c7a-49a6-8663-0e4338e50e34
-- title:
--   Theta Gauss: eq exp of ode
-- statement:
--   The Theta Gauss construction uses the eq exp of ode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DifferentiableFderivApply.lean#L392-L428
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DifferentiableFderivApply.lean#L392-L428

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

theorem GlobalTheory.ThetaGauss.eq_exp_of_ode {h h₁ h₂ : ℂ → ℂ} (hd : ∀ t, HasDerivAt h (h₁ t) t)
    (hd₁ : ∀ t, HasDerivAt h₁ (h₂ t) t) (c : ℂ) (he : ∀ t, h t * h₂ t - h₁ t ^ 2 = c * h t ^ 2)
    (h0 : h 0 ≠ 0) : ∃ α : ℂ, ∀ t, h t = h 0 * Complex.exp (α * t + c / 2 * t ^ 2) := by sorry
