-- Prove2me | Theorems.Thm_GlobalTheory_FrameMeas_borSat_subset_dom
-- name    : GlobalTheory.FrameMeas.borSat_subset_dom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:59:29.288252+00:00
-- url     : https://prove2.me/theorems/1fb4c242-ffed-45b0-9999-62ecd6b9c4c3
-- title:
--   Frame Meas: bor Sat subset dom
-- statement:
--   The Frame Meas construction uses the bor Sat subset dom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MeasurableSetBorSat.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MeasurableSetBorSat.lean#L16-L19

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

theorem GlobalTheory.FrameMeas.borSat_subset_dom {r : ℕ} (X : Data E r) {C : Set (Frame X.Ψ r)} (hC : C ⊆ X.dom) :
    borSat X C ⊆ X.dom := by sorry
