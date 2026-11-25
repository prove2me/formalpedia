-- Prove2me | Theorems.Thm_GlobalTheory_TwoLines_leviCol_eq
-- name    : GlobalTheory.TwoLines.leviCol_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:55:30.516066+00:00
-- url     : https://prove2.me/theorems/5047aff4-89d0-55a4-b0d9-06c2c8db7849
-- title:
--   Two Lines: levi Col eq
-- statement:
--   The Two Lines construction uses the levi Col eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/FirstMinimumBoundedBelow.lean#L31-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/FirstMinimumBoundedBelow.lean#L31-L61

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxC
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FirstMinimumInvariantContinuousPosOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IntegrableMonomialMulConjComplexGaussian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RightMulBorelFirstColumn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FirstMinimumBoundedBelow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ComplexConjugate Matrix
open GlobalTheory GlobalTheory.TwoLines
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.TwoLines.leviCol_eq (X : Data E 2) {x0 : Frame X.Ψ 2} {τ : X.Ψ} (h : (mat x0 τ).det ≠ 0)
    (z : V (nd X)) (ξ : Fin (nd X) → ℂ) :
    0 ≤ leviCol X x0 τ z ξ ∧ (ξ (idx X τ) ≠ 0 → 0 < leviCol X x0 τ z ξ) := by sorry
