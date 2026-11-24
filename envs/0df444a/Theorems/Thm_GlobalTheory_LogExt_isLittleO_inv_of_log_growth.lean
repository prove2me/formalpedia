-- Prove2me | Theorems.Thm_GlobalTheory_LogExt_isLittleO_inv_of_log_growth
-- name    : GlobalTheory.LogExt.isLittleO_inv_of_log_growth
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:19:09.223367+00:00
-- url     : https://prove2.me/theorems/988fcb9b-6de0-4876-82a3-9b0dd45d0f68
-- title:
--   Log Ext: is Little O inv of log growth
-- statement:
--   The Log Ext construction uses the is Little O inv of log growth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RiemannExtensionOfLogGrowth.lean#L13-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RiemannExtensionOfLogGrowth.lean#L13-L61

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FderivIntegralApplyOfHolomorphicOfDominated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RiemannExtensionOfLogGrowth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LogExt
open Filter Topology Asymptotics Metric Set Complex
open scoped Real

theorem GlobalTheory.LogExt.isLittleO_inv_of_log_growth {f g : ℂ → ℂ} {c : ℂ} (hg : AnalyticAt ℂ g c)
    (hne : ¬ ∀ᶠ z in 𝓝 c, g z = 0) {C : ℝ} {k : ℕ}
    (hb : ∀ᶠ z in 𝓝 c, g z ≠ 0 → ‖f z‖ ≤ C * (1 + |Real.log ‖g z‖|) ^ k) :
    (fun z => f z - f c) =o[𝓝[≠] c] fun z => (z - c)⁻¹ := by sorry
