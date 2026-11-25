-- Prove2me | Theorems.Thm_GlobalTheory_JetsPure_monomial_isBigO
-- name    : GlobalTheory.JetsPure.monomial_isBigO
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:35:39.907547+00:00
-- url     : https://prove2.me/theorems/168948c6-0bb5-4df6-bf6a-1988b85d5dc5
-- title:
--   Jets Pure: monomial is Big O
-- statement:
--   The Jets Pure construction uses the monomial is Big O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/SumMultiLtSucc.lean#L15-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/SumMultiLtSucc.lean#L15-L24

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_PointwiseNormConstantSection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_SumMultiLtSucc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.JetsPure
open Filter Asymptotics
open MeasureTheory Topology Filter Asymptotics
open scoped ContDiff ENNReal Matrix

theorem GlobalTheory.JetsPure.monomial_isBigO {n D : ℕ} (σ : Fin D → _root_.ReciprocityTheory.L2DbarEstimates.V n → ℂ)
    (hσ : ∀ k, DifferentiableAt ℂ (σ k) 0) (h0 : ∀ k, σ k 0 = 0) (α : Fin D → ℕ) :
    (fun z => ∏ q, σ q z ^ α q) =O[𝓝 0] fun z => ‖z‖ ^ (∑ q, α q) := by sorry
