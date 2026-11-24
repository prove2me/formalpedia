-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_analyticAt_of_norm_iteratedFDeriv_le
-- name    : GroundTheory.Automorphic.Sobolev.analyticAt_of_norm_iteratedFDeriv_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:34:02.226777+00:00
-- url     : https://prove2.me/theorems/125ab209-f670-4442-83af-aab23eaae02b
-- title:
--   Sobolev: analytic At of norm iterated FDeriv le
-- statement:
--   The Sobolev construction uses the analytic At of norm iterated FDeriv le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/AnalyticHypoSeries.lean#L47-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/AnalyticHypoSeries.lean#L47-L177

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_AnalyticHypoSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open scoped ContDiff NNReal ENNReal Topology
open Set Filter
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

theorem GroundTheory.Automorphic.Sobolev.analyticAt_of_norm_iteratedFDeriv_le {f : E → F} {x₀ : E} {r C M : ℝ} (hr : 0 < r)
    (hf : ContDiffOn ℝ ∞ f (Metric.ball x₀ r))
    (hb : ∀ y ∈ Metric.ball x₀ r, ∀ k : ℕ,
      ‖iteratedFDeriv ℝ k f y‖ ≤ C * M ^ k * k.factorial) :
    AnalyticAt ℝ f x₀ := by sorry
