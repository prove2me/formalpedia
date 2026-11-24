-- Prove2me | Theorems.Thm_GlobalTheory_rpow_neg_le_of_le_mul
-- name    : GlobalTheory.rpow_neg_le_of_le_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:20:36.106365+00:00
-- url     : https://prove2.me/theorems/52a8be69-c501-4cb1-8a41-7ac19b977d73
-- title:
--   Global Theory: rpow neg le of le mul
-- statement:
--   The Global Theory construction uses the rpow neg le of le mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/HeightRpowNegDistortionContraction.lean#L13-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/HeightRpowNegDistortionContraction.lean#L13-L22

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetInequalitiesClosedFormsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsPosLeLatticeHeightAtFrameStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LatticeHeightUpdateFrameComponentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_HeightRpowNegDistortionContraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open GlobalTheory

theorem GlobalTheory.rpow_neg_le_of_le_mul {p q ω δ : ℝ} (hp : 0 < p) (hq : 0 < q) (hω : 0 < ω) (hδ : 0 ≤ δ)
    (h : q ≤ ω * p) : p ^ (-δ) ≤ ω ^ δ * q ^ (-δ) := by sorry
