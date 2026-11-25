-- Prove2me | Theorems.Thm_GlobalTheory_Up_DivInFFPf_phi_le_local
-- name    : GlobalTheory.Up.DivInFFPf.phi_le_local
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T15:54:22.305967+00:00
-- url     : https://prove2.me/theorems/f553be73-d81d-4391-8329-9ab996712809
-- title:
--   Div In FFPf: phi le local
-- statement:
--   The Div In FFPf construction uses the phi le local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MeasurablePhi.lean#L139-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MeasurablePhi.lean#L139-L157

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

theorem GlobalTheory.Up.DivInFFPf.phi_le_local {n : ℕ} (hn : 1 ≤ n) (h : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    phi Xa Fl n h x ≤
      ENNReal.ofReal (X.nfac Xa.Fp x ^ 2 * (∑ k, ‖Xa.w k x‖ ^ 2) ^ (-(1 / 2 : ℝ))) *
        ENNReal.ofReal (‖h x‖ ^ 2 * (∑ k, ‖Fl.s k x‖ ^ 2) ^ (-((n : ℝ) - 1 / 2))) := by sorry
