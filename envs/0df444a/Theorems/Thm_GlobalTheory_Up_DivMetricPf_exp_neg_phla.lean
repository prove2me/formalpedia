-- Prove2me | Theorems.Thm_GlobalTheory_Up_DivMetricPf_exp_neg_phla
-- name    : GlobalTheory.Up.DivMetricPf.exp_neg_phla
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:49:34.556621+00:00
-- url     : https://prove2.me/theorems/289d0d1e-47a3-4aa0-bea7-cfc5b4dae8c7
-- title:
--   Div Metric Pf: exp neg phla
-- statement:
--   The Div Metric Pf construction uses the exp neg phla property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/OfRealRpowNegLe.lean#L18-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/OfRealRpowNegLe.lean#L18-L25

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
open NumberField MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r}

theorem GlobalTheory.Up.DivMetricPf.exp_neg_phla {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom)
    (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) :
    Real.exp (-_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.phla X la x) = X.nfac la x ^ 2 := by sorry
