-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_exists_norm_iteratedFDeriv_le_of_analyticAt
-- name    : GroundTheory.Automorphic.Sobolev.exists_norm_iteratedFDeriv_le_of_analyticAt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:33:52.484891+00:00
-- url     : https://prove2.me/theorems/b95f3692-3d79-4601-8a8e-f5a9869d80d9
-- title:
--   Sobolev: exists norm iterated FDeriv le of analytic At
-- statement:
--   The Sobolev construction uses the exists norm iterated FDeriv le of analytic At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/AnalyticHypoSeries.lean#L240-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/AnalyticHypoSeries.lean#L240-L270

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
  [NormedSpace ℝ F] [CompleteSpace F]

theorem GroundTheory.Automorphic.Sobolev.exists_norm_iteratedFDeriv_le_of_analyticAt {f : E → F} {x₀ : E}
    (hf : AnalyticAt ℝ f x₀) :
    ∃ r > 0, ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ ∀ y ∈ Metric.ball x₀ r, ∀ k : ℕ,
      ‖iteratedFDeriv ℝ k f y‖ ≤ C * M ^ k * k.factorial := by sorry
