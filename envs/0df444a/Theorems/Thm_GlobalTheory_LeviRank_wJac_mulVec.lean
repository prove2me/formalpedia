-- Prove2me | Theorems.Thm_GlobalTheory_LeviRank_wJac_mulVec
-- name    : GlobalTheory.LeviRank.wJac_mulVec
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:48:17.034734+00:00
-- url     : https://prove2.me/theorems/613c94a3-15ab-4d69-9da2-e7363eabcdab
-- title:
--   Levi Rank: w Jac mul Vec
-- statement:
--   The Levi Rank construction uses the w Jac mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsSelectForms.lean#L41-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsSelectForms.lean#L41-L50

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsSelectForms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.L2DbarEstimates Topology
open scoped ContDiff Matrix
open GlobalTheory GlobalTheory.LeviRank

theorem GlobalTheory.LeviRank.wJac_mulVec {n N : ℕ} (w : Fin N → V n → ℂ) (x : V n)
    (hw : ∀ k, DifferentiableAt ℂ (w k) x) (ξ : V n) (k : Fin N) :
    (wJac n N w x *ᵥ ξ.ofLp) k = fderiv ℂ (w k) x ξ := by sorry
