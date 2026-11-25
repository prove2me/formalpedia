-- Prove2me | Theorems.Thm_GlobalTheory_GaugeInt_ip3
-- name    : GlobalTheory.GaugeInt.ip3
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:58:37.661576+00:00
-- url     : https://prove2.me/theorems/90c14ba1-79ae-46dc-8843-d7c7d9b5c43c
-- title:
--   Gauge Int: ip3
-- statement:
--   The Gauge Int construction uses the ip3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CanonGaugeDmonOfHLIntegral.lean#L42-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CanonGaugeDmonOfHLIntegral.lean#L42-L44

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

theorem GlobalTheory.GaugeInt.ip3 {n : ℕ} {a b c : Pt k n d} (ha : IP φ a) (hb : IP φ b) (hc : IP φ c) :
    ∀ j, IP φ (![a, b, c] j) := by sorry
