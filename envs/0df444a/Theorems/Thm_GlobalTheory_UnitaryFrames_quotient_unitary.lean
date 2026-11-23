-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryFrames_quotient_unitary
-- name    : GlobalTheory.UnitaryFrames.quotient_unitary
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:03:24.639022+00:00
-- url     : https://prove2.me/theorems/f422ce43-19ad-4336-b15d-8e23995b72e1
-- title:
--   Unitary Frames: quotient unitary
-- statement:
--   The Unitary Frames construction uses the quotient unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/DetNeZeroOfIsOrth.lean#L108-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/DetNeZeroOfIsOrth.lean#L108-L121

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DetNeZeroOfIsOrth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexConjugate
open GlobalTheory GlobalTheory.UnitaryFrames
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.UnitaryFrames.quotient_unitary {r : ℕ} (X : Data E r) {x y : Frame X.Ψ r} (hx : IsOrth X x)
    (hy : IsOrth X y) :
    X.IsUnitaryC fun τ => ((toGL X hx * (toGL X hy)⁻¹) τ : Matrix (Fin r) (Fin r) ℂ) := by sorry
