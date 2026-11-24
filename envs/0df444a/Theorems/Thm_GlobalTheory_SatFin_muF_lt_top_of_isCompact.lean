-- Prove2me | Theorems.Thm_GlobalTheory_SatFin_muF_lt_top_of_isCompact
-- name    : GlobalTheory.SatFin.muF_lt_top_of_isCompact
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:45:25.869528+00:00
-- url     : https://prove2.me/theorems/f5cace07-7f52-4faa-b7f0-efe9f94d2284
-- title:
--   Sat Fin: mu F lt top of is Compact
-- statement:
--   The Sat Fin construction uses the mu F lt top of is Compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MuFLtTopOfIsCompact.lean#L17-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MuFLtTopOfIsCompact.lean#L17-L28

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MeasurableSetBorSat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MuFLtTopOfIsCompact
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
open GlobalTheory GlobalTheory.SatFin
open GlobalTheory.FrameMeas
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.SatFin.muF_lt_top_of_isCompact {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) {K : Set (V (nd X))}
    (hK : IsCompact K) (hKO : K ⊆ OmF X x0) : muF X x0 K < ⊤ := by sorry
