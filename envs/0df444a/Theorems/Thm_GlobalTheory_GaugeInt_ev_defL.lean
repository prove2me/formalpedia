-- Prove2me | Theorems.Thm_GlobalTheory_GaugeInt_ev_defL
-- name    : GlobalTheory.GaugeInt.ev_defL
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:58:53.051497+00:00
-- url     : https://prove2.me/theorems/9c8a46d2-be44-4840-ade7-98fcb7def3e1
-- title:
--   Gauge Int: ev def L
-- statement:
--   The Gauge Int construction uses the ev def L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CanonGaugeDmonOfHLIntegral.lean#L134-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CanonGaugeDmonOfHLIntegral.lean#L134-L144

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CanonGaugeDmonOfHLIntegral
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
open GlobalTheory.QuadDeriv
open GlobalTheory GlobalTheory.GaugeInt
variable {R k : Type} [CommRing R] [CommRing k] (φ : R →+* k) {d : ℕ}
variable {φ}

theorem GlobalTheory.GaugeInt.ev_defL (F : Pt k 2 d) (hF : GP F) (g : PS k 2 d)
    {n : ℕ} (a b c : Pt k n d) (ha : GP a) (hb : GP b) (hc : GP c) :
    ev ![a, b, c] (defL F g) = ev ![a, c] g + ev ![b, c] g - ev ![addOf F a b, c] g := by sorry
