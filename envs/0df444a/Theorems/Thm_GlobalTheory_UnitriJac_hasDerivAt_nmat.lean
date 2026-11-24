-- Prove2me | Theorems.Thm_GlobalTheory_UnitriJac_hasDerivAt_nmat
-- name    : GlobalTheory.UnitriJac.hasDerivAt_nmat
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:47:45.923031+00:00
-- url     : https://prove2.me/theorems/91612a52-6ab8-42c8-a532-705fad430981
-- title:
--   Unitri Jac: has Deriv At nmat
-- statement:
--   The Unitri Jac construction uses the has Deriv At nmat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/DifferentiableAtAdjugate.lean#L153-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/DifferentiableAtAdjugate.lean#L153-L162

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPfB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_DifferentiableAtAdjugate
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
open GlobalTheory GlobalTheory.UnitriJac
open ReciprocityTheory.ChartRestriction.G.AR.Up.LUPf
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.UnitriJac.hasDerivAt_nmat {r : ℕ} (X : Data E r) {w : ℂ → V (nd X)} {w' : V (nd X)} {t : ℂ}
    (hw : HasDerivAt w w' t) (τ : X.Ψ) (i j : Fin r) :
    HasDerivAt (fun s => mat (nmat X (w s)) τ i j) (lowMat (crd X w' τ) i j) t := by sorry
