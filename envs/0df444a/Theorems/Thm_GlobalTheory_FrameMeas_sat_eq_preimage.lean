-- Prove2me | Theorems.Thm_GlobalTheory_FrameMeas_sat_eq_preimage
-- name    : GlobalTheory.FrameMeas.sat_eq_preimage
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:01:50.869392+00:00
-- url     : https://prove2.me/theorems/e8a7a632-0e06-44da-9309-29148d5db0ae
-- title:
--   Frame Meas: sat eq preimage
-- statement:
--   The Frame Meas construction uses the sat eq preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MeasurableSetBorSat.lean#L66-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MeasurableSetBorSat.lean#L66-L69

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

theorem GlobalTheory.FrameMeas.sat_eq_preimage {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r) {C : Set (Frame X.Ψ r)}
    (hC : C ⊆ X.dom) : sat X x0 C = cpt X x0 ⁻¹' borSat X C := by sorry
