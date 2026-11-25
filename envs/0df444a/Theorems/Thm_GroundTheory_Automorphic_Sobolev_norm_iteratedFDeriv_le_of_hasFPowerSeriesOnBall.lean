-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_iteratedFDeriv_le_of_hasFPowerSeriesOnBall
-- name    : GroundTheory.Automorphic.Sobolev.norm_iteratedFDeriv_le_of_hasFPowerSeriesOnBall
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:33:38.07762+00:00
-- url     : https://prove2.me/theorems/d97cb007-3277-4cbb-a7fa-6fb3809c2c83
-- title:
--   Sobolev: norm iterated FDeriv le of has FPower Series On Ball
-- statement:
--   The Sobolev construction uses the norm iterated FDeriv le of has FPower Series On Ball property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/AnalyticHypoSeries.lean#L186-L201
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/PartialDifferential/AnalyticHypoSeries.lean#L186-L201

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

theorem GroundTheory.Automorphic.Sobolev.norm_iteratedFDeriv_le_of_hasFPowerSeriesOnBall {f : E → F}
    {q : FormalMultilinearSeries ℝ E F} {y : E} {R : ℝ≥0∞} (h : HasFPowerSeriesOnBall f q y R)
    (k : ℕ) : ‖iteratedFDeriv ℝ k f y‖ ≤ k.factorial * ‖q k‖ := by sorry
