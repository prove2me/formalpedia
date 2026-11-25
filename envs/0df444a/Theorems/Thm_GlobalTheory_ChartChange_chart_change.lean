-- Prove2me | Theorems.Thm_GlobalTheory_ChartChange_chart_change
-- name    : GlobalTheory.ChartChange.chart_change
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T02:08:56.895981+00:00
-- url     : https://prove2.me/theorems/9a638567-50d7-4057-a462-9fd233e493a9
-- title:
--   Chart Change: chart change
-- statement:
--   The Chart Change construction uses the chart change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/LintegralBallLtTopOfLocalInverse.lean#L100-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/LintegralBallLtTopOfLocalInverse.lean#L100-L161

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LintegralBallLtTopOfLocalInverse
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
open GlobalTheory GlobalTheory.ChartChange
open Filter
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ExtFPf

theorem GlobalTheory.ChartChange.chart_change : ∀ (r : ℕ) (X : Data E r) (x1 b : Frame X.Ψ r), IsOrth X x1 → b ∈ Bor X.Ψ r →
    ∀ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) →
    ∀ ρ : ℝ, 0 < ρ → ∫⁻ z in Metric.ball (0 : V (nd X)) ρ, φ (cpt X (rmul x1 b) z) < ⊤ →
    ∃ ρ' : ℝ, 0 < ρ' ∧ Metric.ball (0 : V (nd X)) ρ' ⊆ OmF X x1 ∧
      ∫⁻ z in Metric.ball (0 : V (nd X)) ρ', φ (cpt X x1 z) ∂muF X x1 < ⊤ := by sorry
