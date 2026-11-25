-- Prove2me | Theorems.Thm_GlobalTheory_FirstMinimum_cmType_nonempty
-- name    : GlobalTheory.FirstMinimum.cmType_nonempty
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:05:23.965543+00:00
-- url     : https://prove2.me/theorems/4539a7f5-31fa-45e0-9679-8c4d1cd61bee
-- title:
--   First Minimum: cm Type nonempty
-- statement:
--   The First Minimum construction uses the cm Type nonempty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/FirstMinimumInvariantContinuousPos.lean#L13-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/FirstMinimumInvariantContinuousPos.lean#L13-L20

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_PnormInvStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MinimumGrowthBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FirstMinimumInvariantContinuousPos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.FirstMinimum
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.FirstMinimum.cmType_nonempty {r : ℕ} (X : Data E r) : Nonempty X.Ψ := by sorry
