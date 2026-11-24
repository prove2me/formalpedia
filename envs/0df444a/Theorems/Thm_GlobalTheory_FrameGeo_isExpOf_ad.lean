-- Prove2me | Theorems.Thm_GlobalTheory_FrameGeo_isExpOf_ad
-- name    : GlobalTheory.FrameGeo.isExpOf_ad
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:38:16.631796+00:00
-- url     : https://prove2.me/theorems/47dc89a5-7ae6-4c6b-8b85-5ddbd0876b42
-- title:
--   Frame Geo: is Exp Of ad
-- statement:
--   The Frame Geo construction uses the is Exp Of ad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ThreePointSeriesExponentialOfDefect.lean#L172-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ThreePointSeriesExponentialOfDefect.lean#L172-L188

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGoodConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsUniqueNormPrim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowerSeriesExpIntegralCanonGaugeAdditiveSecond
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ThreePointSeriesExponentialOfDefect
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε LPow ThetaGrp IsActOf WeilIs translT GlobalFnsSt)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Good val sval gs)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FrameGeo
open GlobalTheory.FramePull ReciprocityTheory.ChartRestriction.G.TB
variable {R : Type} [CommRing R] {d : ℕ} {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]
variable {O : Type} [CommRing O] [StarRing O] {B : FB R d O} {h : PS k 2 d}

theorem GlobalTheory.FrameGeo.isExpOf_ad (hh : B.IsCanonGauge k h) (a b c : O) :
    IsExpOf (ev ![B.A.act b, B.A.act c] (B.ad a))
      (ev ![B.actK k (a * b), B.actK k c] h - ev ![B.actK k b, B.actK k (star a * c)] h) := by sorry
