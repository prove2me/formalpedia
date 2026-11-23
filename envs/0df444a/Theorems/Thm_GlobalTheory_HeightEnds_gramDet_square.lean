-- Prove2me | Theorems.Thm_GlobalTheory_HeightEnds_gramDet_square
-- name    : GlobalTheory.HeightEnds.gramDet_square
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:26.328494+00:00
-- url     : https://prove2.me/theorems/90d4bc08-7f5a-4634-b44a-92d5ccb16991
-- title:
--   Height Ends: gram Det square
-- statement:
--   The Height Ends construction uses the gram Det square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsPosLeLatticeHeightBotTop.lean#L38-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsPosLeLatticeHeightBotTop.lean#L38-L41

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsBasisMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RelIndexSpanNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsPosLeLatticeHeightBotTop
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
open GlobalTheory GlobalTheory.HeightEnds
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.HeightEnds.gramDet_square {r : ℕ} (N : Matrix (Fin r) (Fin r) ℂ) :
    (Nᴴ * N).det.re = ‖N.det‖ ^ 2 := by sorry
