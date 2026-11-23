-- Prove2me | Theorems.Thm_GlobalTheory_FrameMeas_measurableSet_borSat
-- name    : GlobalTheory.FrameMeas.measurableSet_borSat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:59:38.589601+00:00
-- url     : https://prove2.me/theorems/1d079d5a-1822-4759-b8dd-08a3d6d55601
-- title:
--   Frame Meas: measurable Set bor Sat
-- statement:
--   The Frame Meas construction uses the measurable Set bor Sat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MeasurableSetBorSat.lean#L33-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MeasurableSetBorSat.lean#L33-L64

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_FundSetPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OrthoStatementPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MeasurableSetBorSat
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
open GlobalTheory GlobalTheory.FrameMeas
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.FrameMeas.measurableSet_borSat {r : ℕ} (X : Data E r) {C : Set (Frame X.Ψ r)} (hK : IsCompact C)
    (hC : C ⊆ X.dom) : MeasurableSet (borSat X C) := by sorry
