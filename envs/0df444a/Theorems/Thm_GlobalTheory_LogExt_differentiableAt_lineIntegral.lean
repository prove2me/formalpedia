-- Prove2me | Theorems.Thm_GlobalTheory_LogExt_differentiableAt_lineIntegral
-- name    : GlobalTheory.LogExt.differentiableAt_lineIntegral
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:19:07.11373+00:00
-- url     : https://prove2.me/theorems/a8c27324-9cbc-4863-8318-c2583f7ad96d
-- title:
--   Log Ext: differentiable At line Integral
-- statement:
--   The Log Ext construction uses the differentiable At line Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RiemannExtensionOfLogGrowth.lean#L110-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RiemannExtensionOfLogGrowth.lean#L110-L153

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
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem GlobalTheory.LogExt.differentiableAt_lineIntegral {Ω : Set V} {u : V → ℂ}
    (hu : AnalyticOnNhd ℂ u Ω) {b₀ v : V} {R : ℝ} (hR : 0 < R)
    (hs : ∀ t ∈ sphere (0 : ℂ) R, b₀ + t • v ∈ Ω) :
    DifferentiableAt ℂ (fun b => ∮ t in C(0, R), t⁻¹ • u (b + t • v)) b₀ := by sorry
