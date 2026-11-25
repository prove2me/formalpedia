-- Prove2me | Theorems.Thm_GlobalTheory_GrpSep_rmul_oneF
-- name    : GlobalTheory.GrpSep.rmul_oneF
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:07:06.156353+00:00
-- url     : https://prove2.me/theorems/7bfdb3e2-9ed0-5f28-bfc6-d74b6c717202
-- title:
--   Grp Sep: rmul one F
-- statement:
--   The Grp Sep construction uses the rmul one F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsLeNormDev.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/ExistsLeNormDev.lean#L32-L35

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsLeNormDev
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
open GlobalTheory GlobalTheory.GrpSep
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
omit [NumberField E] [IsCMField E]

theorem GlobalTheory.GrpSep.rmul_oneF {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x : Frame Ψ r) : rmul x (oneF Ψ r) = x := by sorry
