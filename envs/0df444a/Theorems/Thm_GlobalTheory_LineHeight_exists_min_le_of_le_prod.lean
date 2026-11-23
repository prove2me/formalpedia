-- Prove2me | Theorems.Thm_GlobalTheory_LineHeight_exists_min_le_of_le_prod
-- name    : GlobalTheory.LineHeight.exists_min_le_of_le_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:10.800367+00:00
-- url     : https://prove2.me/theorems/b8609a8b-9e8b-40a8-b766-606070ba6125
-- title:
--   Line Height: exists min le of le prod
-- statement:
--   The Line Height construction uses the exists min le of le prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/FirstMinimumLowerOfLineHeights.lean#L23-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/FirstMinimumLowerOfLineHeights.lean#L23-L36

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

theorem GlobalTheory.LineHeight.exists_min_le_of_le_prod {ι : Type} [Fintype ι] [Nonempty ι] (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) (m : ℝ) (hm : m ≤ ∏ i, f i) : ∃ i, min 1 m ≤ f i := by sorry
