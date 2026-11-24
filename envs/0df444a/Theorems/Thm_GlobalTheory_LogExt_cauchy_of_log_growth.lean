-- Prove2me | Theorems.Thm_GlobalTheory_LogExt_cauchy_of_log_growth
-- name    : GlobalTheory.LogExt.cauchy_of_log_growth
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:18:58.463854+00:00
-- url     : https://prove2.me/theorems/4f234869-7518-4f85-b52f-dbca035c664a
-- title:
--   Log Ext: cauchy of log growth
-- statement:
--   The Log Ext construction uses the cauchy of log growth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RiemannExtensionOfLogGrowth.lean#L63-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RiemannExtensionOfLogGrowth.lean#L63-L98

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

theorem GlobalTheory.LogExt.cauchy_of_log_growth {f g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R)) (hg0 : g 0 ≠ 0) (hgs : ∀ t ∈ sphere (0 : ℂ) R, g t ≠ 0)
    (hf : ∀ t ∈ closedBall (0 : ℂ) R, ∀ᶠ z in 𝓝 t, g z ≠ 0 → DifferentiableAt ℂ f z)
    (hb : ∀ t ∈ closedBall (0 : ℂ) R, ∃ (C : ℝ) (k : ℕ),
      ∀ᶠ z in 𝓝 t, g z ≠ 0 → ‖f z‖ ≤ C * (1 + |Real.log ‖g z‖|) ^ k) :
    (∮ t in C(0, R), t⁻¹ • f t) = (2 * π * I : ℂ) • f 0 := by sorry
