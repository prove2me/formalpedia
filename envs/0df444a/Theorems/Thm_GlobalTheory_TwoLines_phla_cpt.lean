-- Prove2me | Theorems.Thm_GlobalTheory_TwoLines_phla_cpt
-- name    : GlobalTheory.TwoLines.phla_cpt
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:29:30.205803+00:00
-- url     : https://prove2.me/theorems/316e70bc-9ccd-467f-9267-ce17e2bc1929
-- title:
--   Two Lines: phla cpt
-- statement:
--   The Two Lines construction uses the phla cpt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/RightMulBorelFirstColumn.lean#L141-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/RightMulBorelFirstColumn.lean#L141-L155

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OrthoStatementPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_EqZeroOfHermOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RightMulBorelFirstColumn
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

theorem GlobalTheory.TwoLines.phla_cpt {X : Data E 2} (hG : X.Gm = 1) (hp : X.p0 = 2) {x0 : Frame X.Ψ 2} (hx : x0 ∈ X.dom)
    (la : Wt X.Ψ 2) (z : V (nd X)) :
    phla X la (cpt X x0 z) = ∑ τ, ((la τ 0 - la τ 1 : ℝ) * Real.log (colSq (cpt X x0 z) τ) +
      (la τ 1 : ℝ) * Real.log (‖(mat x0 τ).det‖ ^ 2)) := by sorry
