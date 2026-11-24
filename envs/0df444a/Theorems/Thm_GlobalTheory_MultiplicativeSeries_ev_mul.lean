-- Prove2me | Theorems.Thm_GlobalTheory_MultiplicativeSeries_ev_mul
-- name    : GlobalTheory.MultiplicativeSeries.ev_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:29:15.106547+00:00
-- url     : https://prove2.me/theorems/c6d42bbf-bd69-4b12-af2b-e748dde708c4
-- title:
--   Multiplicative Series: ev mul
-- statement:
--   The Multiplicative Series construction uses the ev mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EvSelfTwo.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EvSelfTwo.lean#L13-L15

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

theorem GlobalTheory.MultiplicativeSeries.ev_mul {a : Fin m → Pt R n d} (ha : ∀ j i, constantCoeff (a j i) = 0) (f g : PS R m d) :
    ev a (f * g) = ev a f * ev a g := by sorry
