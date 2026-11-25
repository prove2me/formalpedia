-- Prove2me | Theorems.Thm_GlobalTheory_LeviZero_leviV_Lm
-- name    : GlobalTheory.LeviZero.leviV_Lm
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T02:48:19.454153+00:00
-- url     : https://prove2.me/theorems/bc21dd7f-1013-5f0f-aa82-1e507ec43c47
-- title:
--   Levi Zero: levi V Lm
-- statement:
--   The Levi Zero construction uses the levi V Lm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/LeviFormWeightMetricOrthonormalDiagonal.lean#L348-L415
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/LeviFormWeightMetricOrthonormalDiagonal.lean#L348-L415

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LeviFormWeightMetricOrthonormalDiagonal
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
open GlobalTheory GlobalTheory.LeviZero
open Filter
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem GlobalTheory.LeviZero.leviV_Lm {x0 : Frame X.Ψ r} (ho : IsOrth X x0) (ξ : Fin (nd X) → ℂ) (τ : X.Ψ)
    (i : Fin (r + 1)) :
    leviV (nd X) (fun z => ((IW.Lm X (cpt X x0 z) τ i : ℝ) : ℂ)) 0 ξ =
      ∑ a : Fin r, ∑ b : Fin r, if (b : ℕ) < i ∧ (i : ℕ) ≤ a then
        ((sgn X.p0 a * sgn X.p0 b * ‖zMat X ξ τ a b‖ ^ 2 : ℝ) : ℂ) else 0 := by sorry
