-- Prove2me | Theorems.Thm_GlobalTheory_ThetaGauss_frequently_ne_zero
-- name    : GlobalTheory.ThetaGauss.frequently_ne_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:44:48.158803+00:00
-- url     : https://prove2.me/theorems/3f6fd665-cb99-4fd3-bfb8-714f951c9466
-- title:
--   Theta Gauss: frequently ne zero
-- statement:
--   The Theta Gauss construction uses the frequently ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DifferentiableFderivApply.lean#L304-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DifferentiableFderivApply.lean#L304-L309

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

theorem GlobalTheory.ThetaGauss.frequently_ne_zero {θ : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ) (h0 : θ ≠ 0) (z) :
    (𝓝[{x | θ x ≠ 0}] z).NeBot := by sorry
