-- Prove2me | Theorems.Thm_GlobalTheory_Up_DivInFFPf_local_int
-- name    : GlobalTheory.Up.DivInFFPf.local_int
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T15:53:20.833831+00:00
-- url     : https://prove2.me/theorems/7e9f8ae5-4564-41a9-8fc6-274b8774dfea
-- title:
--   Div In FFPf: local int
-- statement:
--   The Div In FFPf construction uses the local int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MeasurablePhi.lean#L159-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MeasurablePhi.lean#L159-L188

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_UpperBounds_SumNormSqWPos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LintegralFundSetInterLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LintegralBallLtTopOfLocalInverse
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_IsOpenSaturation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_OfRealRpowNegLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OrthoStatementPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MeasurablePhi
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal

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
open GlobalTheory GlobalTheory.Up GlobalTheory.Up.DivInFFPf
open Filter
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
variable (Xa : ArchInM X) (Fl : FlatM X Xa)

theorem GlobalTheory.Up.DivInFFPf.local_int {n : ℕ} (hn : 1 ≤ n) (h : Frame X.Ψ r → ℂ) {y : Frame X.Ψ r} (hy : y ∈ X.dom)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hint : ∫⁻ z in Metric.ball (0 : V (nd X)) ρ, ENNReal.ofReal (‖h (cpt X y z)‖ ^ 2 *
      (∑ k, ‖Fl.s k (cpt X y z)‖ ^ 2) ^ (-((n : ℝ) - 1 / 2))) < ⊤) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ ∫⁻ z in Metric.ball (0 : V (nd X)) ρ', phi Xa Fl n h (cpt X y z) < ⊤ := by sorry
