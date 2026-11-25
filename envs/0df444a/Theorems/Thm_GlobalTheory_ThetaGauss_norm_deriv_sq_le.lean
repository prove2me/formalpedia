-- Prove2me | Theorems.Thm_GlobalTheory_ThetaGauss_norm_deriv_sq_le
-- name    : GlobalTheory.ThetaGauss.norm_deriv_sq_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:48:25.851908+00:00
-- url     : https://prove2.me/theorems/878677d9-ef5d-43d6-8542-0053efe06d83
-- title:
--   Theta Gauss: norm deriv sq le
-- statement:
--   The Theta Gauss construction uses the norm deriv sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DifferentiableFderivApply.lean#L86-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DifferentiableFderivApply.lean#L86-L106

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

theorem GlobalTheory.ThetaGauss.norm_deriv_sq_le {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    (hm : ∀ s, h s = 0 → deriv h s = 0) {r M δ : ℝ} (hr : 0 < r) (hr' : r ≤ 1 / 2) (hδ : 0 < δ)
    (hM : ∀ t ∈ closedBall (0 : ℂ) 1, ‖h t‖ ≤ M) (hl : ∀ t ∈ sphere (0 : ℂ) r, δ ≤ ‖h t‖) :
    ‖deriv h 0 ^ 2‖ ≤ (2 * M) ^ 2 / δ * ‖h 0‖ := by sorry
