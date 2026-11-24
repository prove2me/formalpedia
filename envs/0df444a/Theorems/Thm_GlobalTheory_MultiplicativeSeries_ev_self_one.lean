-- Prove2me | Theorems.Thm_GlobalTheory_MultiplicativeSeries_ev_self_one
-- name    : GlobalTheory.MultiplicativeSeries.ev_self_one
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:28:55.997412+00:00
-- url     : https://prove2.me/theorems/d1da0232-cd48-43bb-a548-0bf90ccf011d
-- title:
--   Multiplicative Series: ev self one
-- statement:
--   The Multiplicative Series construction uses the ev self one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EvSelfTwo.lean#L22-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EvSelfTwo.lean#L22-L29

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EvSelfTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.MultiplicativeSeries
open GlobalTheory.GaugeAdjoint
variable {R : Type} [CommRing R] {d m n : ℕ}

theorem GlobalTheory.MultiplicativeSeries.ev_self_one (f : PS R 1 d) : ev (n := 1) ![pt R d 0] f = f := by sorry
