-- Prove2me | Theorems.Thm_GlobalTheory_JetSer_IntTrans_map_ev2
-- name    : GlobalTheory.JetSer.IntTrans.map_ev2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:53:37.930722+00:00
-- url     : https://prove2.me/theorems/e595a845-451b-48dc-bc43-33957ef8c4e9
-- title:
--   Int Trans: map ev2
-- statement:
--   The Int Trans construction uses the map ev2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/RelatedMap.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/RelatedMap.lean#L33-L37

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

theorem GlobalTheory.JetSer.IntTrans.map_ev2 {n : ℕ} {a b : Pt R n d} (ha : GP a) (hb : GP b) (g : PS R 2 d) :
    MvPowerSeries.map f (ev ![a, b] g) = ev ![mP f a, mP f b] (MvPowerSeries.map f g) := by sorry
