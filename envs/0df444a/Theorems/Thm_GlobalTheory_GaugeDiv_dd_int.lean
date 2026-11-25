-- Prove2me | Theorems.Thm_GlobalTheory_GaugeDiv_dd_int
-- name    : GlobalTheory.GaugeDiv.dd_int
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:47:59.151821+00:00
-- url     : https://prove2.me/theorems/1c5d925a-86bd-4a00-a739-ea0ce52cfab5
-- title:
--   Gauge Div: dd int
-- statement:
--   The Gauge Div construction uses the dd int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ThirdPointDerivativeAtZeroSeriesMemIntegral.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ThirdPointDerivativeAtZeroSeriesMemIntegral.lean#L32-L35

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

theorem GlobalTheory.GaugeDiv.dd_int {F : Pt k 2 d} (hF : IP φ F) (a : Fin 2) {v : Fin d → k} (hv : ∀ i, v i ∈ φ.range)
    {G : PS k 2 d} (hG : G ∈ IntS φ 2 d) : DD F a v G ∈ IntS φ 2 d := by sorry
