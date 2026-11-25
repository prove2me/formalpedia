-- Prove2me | Theorems.Thm_GlobalTheory_ThetaGauss_analytic_of_diff
-- name    : GlobalTheory.ThetaGauss.analytic_of_diff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:43:41.615225+00:00
-- url     : https://prove2.me/theorems/2507fc89-c7d8-4907-900a-c638b0d8153a
-- title:
--   Theta Gauss: analytic of diff
-- statement:
--   The Theta Gauss construction uses the analytic of diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DifferentiableFderivApply.lean#L110-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DifferentiableFderivApply.lean#L110-L112

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

theorem GlobalTheory.ThetaGauss.analytic_of_diff {f : (Fin g → ℂ) → ℂ} (hf : Differentiable ℂ f) :
    AnalyticOnNhd ℂ f Set.univ := by sorry
