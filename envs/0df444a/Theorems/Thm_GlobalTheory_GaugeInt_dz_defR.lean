-- Prove2me | Theorems.Thm_GlobalTheory_GaugeInt_dz_defR
-- name    : GlobalTheory.GaugeInt.dz_defR
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:58:45.246462+00:00
-- url     : https://prove2.me/theorems/42a3b206-6559-4be1-822f-8d268491be40
-- title:
--   Gauge Int: dz def R
-- statement:
--   The Gauge Int construction uses the dz def R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CanonGaugeDmonOfHLIntegral.lean#L168-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CanonGaugeDmonOfHLIntegral.lean#L168-L176

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

theorem GlobalTheory.GaugeInt.dz_defR {F : Pt k 2 d} (hF : IP φ F) (g : PS k 2 d) (h : DI φ (defR F g))
    {a b : Pt k 2 d} (ha : IP φ a) (hb : IP φ b) (i : Fin d) :
    ev ![0, a] (pderiv k ((0 : Fin 2), i) g) + ev ![0, b] (pderiv k ((0 : Fin 2), i) g) -
      ev ![0, addOf F a b] (pderiv k ((0 : Fin 2), i) g) ∈ IntS φ 2 d := by sorry
