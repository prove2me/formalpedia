-- Prove2me | Theorems.Thm_GlobalTheory_JetSer_isFPt_of_isUnivChart
-- name    : GlobalTheory.JetSer.isFPt_of_isUnivChart
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:16:15.248645+00:00
-- url     : https://prove2.me/theorems/12099600-556d-4d07-ad4b-52a273170303
-- title:
--   Jet Ser: is FPt of is Univ Chart
-- statement:
--   The Jet Ser construction uses the is FPt of is Univ Chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/RepJetAugCompTrunc.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/RepJetAugCompTrunc.lean#L20-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_RepJetAugCompTrunc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetSer
variable {R : Type} [CommRing R]

theorem GlobalTheory.JetSer.isFPt_of_isUnivChart {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {d : ℕ} {x : Fam G (Fin d)}
    (hx : IsUnivChart G d x) : IsFPt x := by sorry
