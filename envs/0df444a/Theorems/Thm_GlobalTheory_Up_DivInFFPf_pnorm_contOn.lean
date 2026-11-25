-- Prove2me | Theorems.Thm_GlobalTheory_Up_DivInFFPf_pnorm_contOn
-- name    : GlobalTheory.Up.DivInFFPf.pnorm_contOn
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:53:31.514531+00:00
-- url     : https://prove2.me/theorems/2939fe5a-8247-40e4-91d2-fd990f5d8e66
-- title:
--   Div In FFPf: pnorm cont On
-- statement:
--   The Div In FFPf construction uses the pnorm cont On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MeasurablePhi.lean#L93-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MeasurablePhi.lean#L93-L95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_UpperBounds_SumNormSqWPos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LintegralFundSetInterLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LintegralBallLtTopOfLocalInverse
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_IsOpenSaturation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_OfRealRpowNegLe
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OrthoStatementPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MeasurablePhi
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

theorem GlobalTheory.Up.DivInFFPf.pnorm_contOn {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : X.IsSec la P) :
    ContinuousOn (X.pnorm la P) X.dom := by sorry
