-- Prove2me | Theorems.Thm_GlobalTheory_taylorDir_fderiv_sum
-- name    : GlobalTheory.taylorDir_fderiv_sum
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:50:59.539244+00:00
-- url     : https://prove2.me/theorems/3b93b5fb-c963-5d2f-bddd-e88b91189fe0
-- title:
--   Global Theory: taylor Dir fderiv sum
-- statement:
--   The Global Theory construction uses the taylor Dir fderiv sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/MemAnalyticAtZeroOfEventuallyDifferentiableAt.lean#L346-L354
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/MemAnalyticAtZeroOfEventuallyDifferentiableAt.lean#L346-L354

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LineDerivListEqIteratedFDeriv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_MemAnalyticAtZeroOfEventuallyDifferentiableAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
variable {σ W : Type*} [Fintype σ] [NormedAddCommGroup W] [NormedSpace ℂ W]
variable (u : σ → W) {f g : W → ℂ}

theorem GlobalTheory.taylorDir_fderiv_sum (hf : AnalyticAt ℂ f 0) (a : σ → ℂ) :
    taylorDir u (fun z => fderiv ℂ f z (∑ i, a i • u i)) =
      ∑ i, a i • MvPowerSeries.pderiv ℂ i (taylorDir u f) := by sorry
