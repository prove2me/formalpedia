-- Prove2me | Theorems.Thm_GlobalTheory_taylorDir_eq_taylor
-- name    : GlobalTheory.taylorDir_eq_taylor
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:51:44.803337+00:00
-- url     : https://prove2.me/theorems/28af7023-ede4-4791-909b-9b9a811e89e0
-- title:
--   Global Theory: taylor Dir eq taylor
-- statement:
--   The Global Theory construction uses the taylor Dir eq taylor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/MemAnalyticAtZeroOfEventuallyDifferentiableAt.lean#L452-L458
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/MemAnalyticAtZeroOfEventuallyDifferentiableAt.lean#L452-L458

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
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable {f g : (σ → ℂ) → ℂ}
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem GlobalTheory.taylorDir_eq_taylor (u : σ → W) {F : W → ℂ} (hF : AnalyticAt ℂ F 0) :
    taylorDir u F = taylor fun z : σ → ℂ => F (∑ i, z i • u i) := by sorry
