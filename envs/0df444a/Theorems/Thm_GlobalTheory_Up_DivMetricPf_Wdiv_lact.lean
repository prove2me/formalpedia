-- Prove2me | Theorems.Thm_GlobalTheory_Up_DivMetricPf_Wdiv_lact
-- name    : GlobalTheory.Up.DivMetricPf.Wdiv_lact
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T15:50:42.188819+00:00
-- url     : https://prove2.me/theorems/83f6bda7-33d5-4446-83e7-e1c7cfa13638
-- title:
--   Div Metric Pf: Wdiv lact
-- statement:
--   The Div Metric Pf construction uses the Wdiv lact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/OfRealRpowNegLe.lean#L144-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/OfRealRpowNegLe.lean#L144-L150

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_UpperBounds_SumNormSqWPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_PnormInvStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_OfRealRpowNegLe
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
open GlobalTheory GlobalTheory.Up GlobalTheory.Up.DivMetricPf
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
variable (Xa : ArchInM X) (Fl : FlatM X Xa) (n : ℕ)

theorem GlobalTheory.Up.DivMetricPf.Wdiv_lact (hN : NfacLactStatement (E := E)) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) : Wdiv X Xa Fl n (lact γ x) = Wdiv X Xa Fl n x := by sorry
