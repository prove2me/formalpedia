-- Prove2me | Theorems.Thm_GlobalTheory_ChartCount_card_strictLower
-- name    : GlobalTheory.ChartCount.card_strictLower
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:36:27.781104+00:00
-- url     : https://prove2.me/theorems/7a09bb37-9aae-49dc-ae35-a781efba8495
-- title:
--   Chart Count: card strict Lower
-- statement:
--   The Chart Count construction uses the card strict Lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TotallyRealDegreeAndChartDimensionEq.lean#L10-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TotallyRealDegreeAndChartDimensionEq.lean#L10-L19

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

theorem GlobalTheory.ChartCount.card_strictLower (r : ℕ) : Fintype.card {p : Fin r × Fin r // p.2 < p.1} = r * (r - 1) / 2 := by sorry
