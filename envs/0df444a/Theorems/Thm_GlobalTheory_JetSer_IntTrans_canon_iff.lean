-- Prove2me | Theorems.Thm_GlobalTheory_JetSer_IntTrans_canon_iff
-- name    : GlobalTheory.JetSer.IntTrans.canon_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:42:59.866596+00:00
-- url     : https://prove2.me/theorems/880be239-b17c-4a68-a254-e87fd85d45b6
-- title:
--   Int Trans: canon iff
-- statement:
--   The Int Trans construction uses the canon iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/RelatedMap.lean#L209-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/RelatedMap.lean#L209-L230

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_RelatedMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.JetSer
open GlobalTheory GlobalTheory.JetSer GlobalTheory.JetSer.IntTrans
variable {R k : Type} [CommRing R] [CommRing k] [Algebra ℚ k] [Algebra R k] {d : ℕ}
  {O : Type} [CommRing O] [StarRing O] {B : FB R d O} {C : FB k d O}

theorem GlobalTheory.JetSer.IntTrans.canon_iff (hF : C.G.F = mP (algebraMap R k) B.G.F) (hA : ∀ a, C.A.act a = mP (algebraMap R k) (B.A.act a))
    (h1 : C.ph1 = MvPowerSeries.map (algebraMap R k) B.ph1) (h2 : C.ph2 = MvPowerSeries.map (algebraMap R k) B.ph2)
    (hs : C.sy = MvPowerSeries.map (algebraMap R k) B.sy)
    (hd : ∀ a, C.ad a = MvPowerSeries.map (algebraMap R k) (B.ad a)) (h : PS k 2 d) :
    C.IsCanonGauge k h ↔ B.IsCanonGauge k h := by sorry
