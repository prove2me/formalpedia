-- Prove2me | Theorems.Thm_GlobalTheory_JetSer_IntTrans_related_map
-- name    : GlobalTheory.JetSer.IntTrans.related_map
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:42:11.954379+00:00
-- url     : https://prove2.me/theorems/679be6ee-e036-40c9-8608-aac1d039f821
-- title:
--   Int Trans: related map
-- statement:
--   The Int Trans construction uses the related map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/RelatedMap.lean#L60-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/RelatedMap.lean#L60-L112

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
variable {R k : Type} [CommRing R] [CommRing k] (f : R →+* k) {d : ℕ}

theorem GlobalTheory.JetSer.IntTrans.related_map {O : Type} [CommRing O] [StarRing O] {B B' : FB R d O} {φ φi : Pt R 1 d} {ε : PS R 2 d}
    (h : Related B B' φ φi ε) {C C' : FB k d O}
    (hF : C.G.F = mP f B.G.F) (hA : ∀ a, C.A.act a = mP f (B.A.act a))
    (h1 : C.ph1 = MvPowerSeries.map f B.ph1) (h2 : C.ph2 = MvPowerSeries.map f B.ph2)
    (hs : C.sy = MvPowerSeries.map f B.sy) (hd : ∀ a, C.ad a = MvPowerSeries.map f (B.ad a))
    (hF' : C'.G.F = mP f B'.G.F) (hA' : ∀ a, C'.A.act a = mP f (B'.A.act a))
    (h1' : C'.ph1 = MvPowerSeries.map f B'.ph1) (h2' : C'.ph2 = MvPowerSeries.map f B'.ph2)
    (hs' : C'.sy = MvPowerSeries.map f B'.sy) (hd' : ∀ a, C'.ad a = MvPowerSeries.map f (B'.ad a)) :
    Related C C' (mP f φ) (mP f φi) (MvPowerSeries.map f ε) := by sorry
