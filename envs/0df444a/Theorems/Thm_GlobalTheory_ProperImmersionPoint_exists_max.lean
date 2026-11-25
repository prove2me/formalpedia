-- Prove2me | Theorems.Thm_GlobalTheory_ProperImmersionPoint_exists_max
-- name    : GlobalTheory.ProperImmersionPoint.exists_max
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:50:58.863046+00:00
-- url     : https://prove2.me/theorems/55122c2d-efa6-5cfa-93a7-d117e6aad6a9
-- title:
--   Proper Immersion Point: exists max
-- statement:
--   The Proper Immersion Point construction uses the exists max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/CptDifferentiable.lean#L89-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/CptDifferentiable.lean#L89-L127

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpolationModelInequalities
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_PointwiseNormInvarianceHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfS
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsSelectForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_CptDifferentiable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.ProperImmersionPoint
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.ProperImmersionPoint.exists_max {r : ℕ} {X : Data E r} {L eW : Wt X.Ψ r} {N a : ℕ}
    {w : Fin N → Frame X.Ψ r → ℂ} {et : Frame X.Ψ r → ℂ}
    (hw : ∀ k, X.IsSec L (w k)) (hnz : ∀ x ∈ X.dom, ∃ k, w k x ≠ 0) (het : X.IsSec eW et)
    (hne : ∃ x ∈ X.dom, et x ≠ 0)
    (hprop : ∀ δ : ℝ, 0 < δ → ∃ C : Set (Frame X.Ψ r), IsCompact C ∧ C ⊆ X.dom ∧ ∀ x ∈ X.dom,
      δ * (∑ k, X.pnorm L (w k) x ^ 2) ^ a ≤ X.pnorm eW et x ^ 2 →
        ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ C) :
    ∃ x ∈ X.dom, et x ≠ 0 ∧ ∀ y ∈ X.dom, ratio X L eW a w et y ≤ ratio X L eW a w et x := by sorry
