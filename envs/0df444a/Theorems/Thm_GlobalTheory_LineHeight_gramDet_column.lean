-- Prove2me | Theorems.Thm_GlobalTheory_LineHeight_gramDet_column
-- name    : GlobalTheory.LineHeight.gramDet_column
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:58.247859+00:00
-- url     : https://prove2.me/theorems/f056bbd9-cd83-4d9c-858e-f9dd60649da1
-- title:
--   Line Height: gram Det column
-- statement:
--   The Line Height construction uses the gram Det column property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/FirstMinimumLowerOfLineHeights.lean#L13-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/FirstMinimumLowerOfLineHeights.lean#L13-L21

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LatDen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RelIndexSpanNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MajorantEqSumNormSqOrthonormalFrameStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FirstMinimumLowerOfLineHeights
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
open GlobalTheory GlobalTheory.LineHeight

theorem GlobalTheory.LineHeight.gramDet_column {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (u : Fin r → ℂ) :
    (((A * (Matrix.of fun k (_ : Unit) => u k))ᴴ * (A * (Matrix.of fun k (_ : Unit) => u k))).det.re)
      = ∑ a, ‖(A.mulVec u) a‖ ^ 2 := by sorry
