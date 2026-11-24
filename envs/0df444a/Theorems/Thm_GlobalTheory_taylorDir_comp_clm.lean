-- Prove2me | Theorems.Thm_GlobalTheory_taylorDir_comp_clm
-- name    : GlobalTheory.taylorDir_comp_clm
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:43:18.884404+00:00
-- url     : https://prove2.me/theorems/4c5e056a-206d-463a-86fc-6e63ff9a63ca
-- title:
--   Global Theory: taylor Dir comp clm
-- statement:
--   The Global Theory construction uses the taylor Dir comp clm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/MemAnalyticAtZeroOfEventuallyDifferentiableAt.lean#L228-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/MemAnalyticAtZeroOfEventuallyDifferentiableAt.lean#L228-L238

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

theorem GlobalTheory.taylorDir_comp_clm {W' : Type*} [NormedAddCommGroup W'] [NormedSpace ℂ W']
    (L : W' →L[ℂ] W) (v : σ → W') (hf : AnalyticAt ℂ f 0) :
    taylorDir v (fun z => f (L z)) = taylorDir (fun i => L (v i)) f := by sorry
