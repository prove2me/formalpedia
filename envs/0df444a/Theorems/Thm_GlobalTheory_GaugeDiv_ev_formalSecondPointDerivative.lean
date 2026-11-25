-- Prove2me | Theorems.Thm_GlobalTheory_GaugeDiv_ev_formalSecondPointDerivative
-- name    : GlobalTheory.GaugeDiv.ev_formalSecondPointDerivative
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:44:41.274055+00:00
-- url     : https://prove2.me/theorems/4146c986-012e-4820-91cb-d993a57a3745
-- title:
--   Gauge Div: ev formal Second Point Derivative
-- statement:
--   The Gauge Div construction uses the ev formal Second Point Derivative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ThirdPointDerivativeAtZeroSeriesMemIntegral.lean#L53-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ThirdPointDerivativeAtZeroSeriesMemIntegral.lean#L53-L58

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CanonGaugeDmonOfHLIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_CoeffSingleLawAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ThirdPointDerivativeAtZeroSeriesMemIntegral
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
open GlobalTheory.QuadDeriv GlobalTheory.GaugeInt
open GlobalTheory GlobalTheory.GaugeDiv
variable {R k : Type} [CommRing R] [CommRing k] {φ : R →+* k} {d : ℕ}

theorem GlobalTheory.GaugeDiv.ev_formalSecondPointDerivative {n : ℕ} (a : Pt k n d) (ha : GP a) (v : Fin d → k) (f : PS k 2 d) :
    ev ![a] (dy v f) = ∑ i, C (v i) * ev ![a, 0] (pderiv k ((1 : Fin 2), i) f) := by sorry
