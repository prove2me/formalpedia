-- Prove2me | Theorems.Thm_GlobalTheory_ThetaGauss_differentiable_fderiv_apply
-- name    : GlobalTheory.ThetaGauss.differentiable_fderiv_apply
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T00:48:46.299866+00:00
-- url     : https://prove2.me/theorems/0214f3bd-b780-425b-80bb-04fca7320b0a
-- title:
--   Theta Gauss: differentiable fderiv apply
-- statement:
--   The Theta Gauss construction uses the differentiable fderiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DifferentiableFderivApply.lean#L370-L373
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DifferentiableFderivApply.lean#L370-L373

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

theorem GlobalTheory.ThetaGauss.differentiable_fderiv_apply {θ : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ)
    (v : Fin g → ℂ) : Differentiable ℂ fun z => fderiv ℂ θ z v := by sorry
