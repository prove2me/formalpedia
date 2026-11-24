-- Prove2me | Theorems.Thm_GlobalTheory_ConeImage_differentiable_eval
-- name    : GlobalTheory.ConeImage.differentiable_eval
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:25:46.127961+00:00
-- url     : https://prove2.me/theorems/3c03d1fa-cc75-451f-b2df-32d04dd79fd5
-- title:
--   Cone Image: differentiable eval
-- statement:
--   The Cone Image construction uses the differentiable eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsNhdsSubsetRange.lean#L250-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsNhdsSubsetRange.lean#L250-L256

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsNhdsSubsetRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ConeImage

theorem GlobalTheory.ConeImage.differentiable_eval {W ι : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    {f : W → ι → ℂ} (hf : ∀ c, Differentiable ℂ fun w => f w c) (F : MvPolynomial ι ℂ) :
    Differentiable ℂ fun w => MvPolynomial.eval (f w) F := by sorry
