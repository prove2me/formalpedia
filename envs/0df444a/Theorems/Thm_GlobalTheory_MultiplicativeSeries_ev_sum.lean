-- Prove2me | Theorems.Thm_GlobalTheory_MultiplicativeSeries_ev_sum
-- name    : GlobalTheory.MultiplicativeSeries.ev_sum
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:29:00.664324+00:00
-- url     : https://prove2.me/theorems/e5855f3e-8f99-4412-a27d-18631de81ac3
-- title:
--   Multiplicative Series: ev sum
-- statement:
--   The Multiplicative Series construction uses the ev sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EvSelfTwo.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/EvSelfTwo.lean#L17-L20

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

theorem GlobalTheory.MultiplicativeSeries.ev_sum {a : Fin m → Pt R n d} (ha : ∀ j i, constantCoeff (a j i) = 0) {ι : Type}
    (t : Finset ι) (f : ι → PS R m d) : ev a (∑ i ∈ t, f i) = ∑ i ∈ t, ev a (f i) := by sorry
