-- Prove2me | Theorems.Thm_GlobalTheory_JetSer_Related_refl
-- name    : GlobalTheory.JetSer.Related.refl
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:35.908806+00:00
-- url     : https://prove2.me/theorems/8028419f-cf6a-4737-8de4-9bcb92de1eea
-- title:
--   Related: refl
-- statement:
--   The Related construction uses the refl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwoChartAtlas/TwoChartSt.lean#L264-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwoChartAtlas/TwoChartSt.lean#L264-L288

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLawPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
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
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetSer
variable {R : Type} [CommRing R]
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε zero2)
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair)
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

theorem GlobalTheory.JetSer.Related.refl {d : ℕ} {O : Type} [CommRing O] [StarRing O] (B : FB R d O) :
    Related B B (pt R (n := 1) d 0) (pt R (n := 1) d 0) 1 := by sorry
