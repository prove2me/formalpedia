-- Prove2me | Theorems.Thm_GlobalTheory_GaugeInt_dz_defL
-- name    : GlobalTheory.GaugeInt.dz_defL
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:58:32.502471+00:00
-- url     : https://prove2.me/theorems/d4214858-6365-4b4a-b09a-5b7da36ad24c
-- title:
--   Gauge Int: dz def L
-- statement:
--   The Gauge Int construction uses the dz def L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CanonGaugeDmonOfHLIntegral.lean#L158-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/CanonGaugeDmonOfHLIntegral.lean#L158-L166

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

theorem GlobalTheory.GaugeInt.dz_defL {F : Pt k 2 d} (hF : IP φ F) (g : PS k 2 d) (h : DI φ (defL F g))
    {a b : Pt k 2 d} (ha : IP φ a) (hb : IP φ b) (i : Fin d) :
    ev ![a, 0] (pderiv k ((1 : Fin 2), i) g) + ev ![b, 0] (pderiv k ((1 : Fin 2), i) g) -
      ev ![addOf F a b, 0] (pderiv k ((1 : Fin 2), i) g) ∈ IntS φ 2 d := by sorry
