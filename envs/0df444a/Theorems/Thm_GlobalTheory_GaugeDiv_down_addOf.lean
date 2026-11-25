-- Prove2me | Theorems.Thm_GlobalTheory_GaugeDiv_down_addOf
-- name    : GlobalTheory.GaugeDiv.down_addOf
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:44:14.785615+00:00
-- url     : https://prove2.me/theorems/f6ab0834-ab56-4473-acde-b9c25040b05d
-- title:
--   Gauge Div: down add Of
-- statement:
--   The Gauge Div construction uses the down add Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ThirdPointDerivativeAtZeroSeriesMemIntegral.lean#L113-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ThirdPointDerivativeAtZeroSeriesMemIntegral.lean#L113-L123

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

theorem GlobalTheory.GaugeDiv.down_addOf {F : Pt k 2 d} (hU : evP (n := 1) ![pt k d 0, 0] F = pt k d 0) (a : Fin 2) :
    evP (n := 2) ![pt k d 0, pt k d 1, 0] (addOf F (up (pt k d a)) (pt k d 2)) = pt k d a := by sorry
