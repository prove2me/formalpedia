-- Prove2me | Theorems.Thm_GlobalTheory_ChartCount_fdeg_and_nd
-- name    : GlobalTheory.ChartCount.fdeg_and_nd
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:59:28.364638+00:00
-- url     : https://prove2.me/theorems/d175cd0a-f639-47e4-a6c5-8747e3a9b96d
-- title:
--   Chart Count: fdeg and nd
-- statement:
--   The Chart Count construction uses the fdeg and nd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TotallyRealDegreeAndChartDimensionEq.lean#L45-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TotallyRealDegreeAndChartDimensionEq.lean#L45-L53

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__TamagawaSpecialUnitary_320f37a25cd91d38
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PhaseFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TotallyRealDegreeAndChartDimensionEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal
open GlobalTheory GlobalTheory.ChartCount

theorem GlobalTheory.ChartCount.fdeg_and_nd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    fdeg E = X.Ψ.card ∧ nd X = X.Ψ.card * (r * (r - 1) / 2) := by sorry
