-- Prove2me | Theorems.Thm_GlobalTheory_GaugeBaseChange_map_ev_two
-- name    : GlobalTheory.GaugeBaseChange.map_ev_two
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:42:21.748393+00:00
-- url     : https://prove2.me/theorems/0b4148d7-97a0-4c9b-9a03-1a817505f0b9
-- title:
--   Gauge Base Change: map ev two
-- statement:
--   The Gauge Base Change construction uses the map ev two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/CanonGaugeNabValBaseChange.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/CanonGaugeNabValBaseChange.lean#L23-L27

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MapDofIterate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonGaugeNabValBaseChange
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory GlobalTheory.GaugeBaseChange
open GlobalTheory.QuadDeriv
variable {k k' : Type} [CommRing k] [CommRing k'] (φ : k →+* k') {d : ℕ}

theorem GlobalTheory.GaugeBaseChange.map_ev_two {n : ℕ} (a b : Pt k n d) (ha : GP a) (hb : GP b) (f : PS k 2 d) :
    MvPowerSeries.map φ (ev ![a, b] f) = ev ![mapP φ a, mapP φ b] (MvPowerSeries.map φ f) := by sorry
