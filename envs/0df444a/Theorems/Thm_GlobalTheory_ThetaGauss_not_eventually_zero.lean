-- Prove2me | Theorems.Thm_GlobalTheory_ThetaGauss_not_eventually_zero
-- name    : GlobalTheory.ThetaGauss.not_eventually_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:43:58.033992+00:00
-- url     : https://prove2.me/theorems/87aad6eb-9d4e-4f94-83d2-19e2919caa7b
-- title:
--   Theta Gauss: not eventually zero
-- statement:
--   The Theta Gauss construction uses the not eventually zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DifferentiableFderivApply.lean#L182-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DifferentiableFderivApply.lean#L182-L186

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

theorem GlobalTheory.ThetaGauss.not_eventually_zero {h : ℂ → ℂ} (hh : Differentiable ℂ h) (h0 : ∃ s, h s ≠ 0) (s₀ : ℂ) :
    ¬ ∀ᶠ s in 𝓝 s₀, h s = 0 := by sorry
