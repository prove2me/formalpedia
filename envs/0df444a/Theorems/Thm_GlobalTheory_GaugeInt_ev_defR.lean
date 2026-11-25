-- Prove2me | Theorems.Thm_GlobalTheory_GaugeInt_ev_defR
-- name    : GlobalTheory.GaugeInt.ev_defR
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:58:49.426538+00:00
-- url     : https://prove2.me/theorems/10f79d92-4b1f-4c5f-8b96-a7722338b837
-- title:
--   Gauge Int: ev def R
-- statement:
--   The Gauge Int construction uses the ev def R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CanonGaugeDmonOfHLIntegral.lean#L146-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CanonGaugeDmonOfHLIntegral.lean#L146-L156

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

theorem GlobalTheory.GaugeInt.ev_defR (F : Pt k 2 d) (hF : GP F) (g : PS k 2 d)
    {n : ℕ} (a b c : Pt k n d) (ha : GP a) (hb : GP b) (hc : GP c) :
    ev ![a, b, c] (defR F g) = ev ![a, b] g + ev ![a, c] g - ev ![a, addOf F b c] g := by sorry
