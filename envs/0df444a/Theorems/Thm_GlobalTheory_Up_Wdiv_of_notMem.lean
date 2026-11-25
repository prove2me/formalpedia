-- Prove2me | Theorems.Thm_GlobalTheory_Up_Wdiv_of_notMem
-- name    : GlobalTheory.Up.Wdiv_of_notMem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:27:42.152851+00:00
-- url     : https://prove2.me/theorems/7aff8c8d-0cb5-467a-aaa2-7508558fc6a4
-- title:
--   Up: Wdiv of not Mem
-- statement:
--   The Up construction uses the Wdiv of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/UpperBounds/SumNormSqWPos.lean#L61-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/UpperBounds/SumNormSqWPos.lean#L61-L63

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_UpperBounds_SumNormSqWPos
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
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open GlobalTheory GlobalTheory.Up
variable {r : ℕ} {X : Data E r} (Xa : ArchInM X) (Fl : FlatM X Xa) (n : ℕ) {x : Frame X.Ψ r}

theorem GlobalTheory.Up.Wdiv_of_notMem (hx : x ∉ X.dom) : Wdiv X Xa Fl n x = 0 := by sorry
