-- Prove2me | Theorems.Thm_GlobalTheory_UnitaryFrames_isClosed_unitary
-- name    : GlobalTheory.UnitaryFrames.isClosed_unitary
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:04:41.496868+00:00
-- url     : https://prove2.me/theorems/58da2b89-579e-4666-abc2-ed130d208fa7
-- title:
--   Unitary Frames: is Closed unitary
-- statement:
--   The Unitary Frames construction uses the is Closed unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/DetNeZeroOfIsOrth.lean#L69-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/DetNeZeroOfIsOrth.lean#L69-L78

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

theorem GlobalTheory.UnitaryFrames.isClosed_unitary {r : ℕ} (X : Data E r) :
    IsClosed {g : X.Ψ → GL (Fin r) ℂ | X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)} := by sorry
