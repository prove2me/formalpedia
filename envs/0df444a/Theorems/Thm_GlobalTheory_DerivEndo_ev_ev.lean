-- Prove2me | Theorems.Thm_GlobalTheory_DerivEndo_ev_ev
-- name    : GlobalTheory.DerivEndo.ev_ev
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:12:55.70875+00:00
-- url     : https://prove2.me/theorems/81bdaaac-82a2-47e9-bcb1-afaa953e9509
-- title:
--   Deriv Endo: ev ev
-- statement:
--   The Deriv Endo construction uses the ev ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/GermPointsNoConstantTermFirstZero.lean#L79-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/GermPointsNoConstantTermFirstZero.lean#L79-L83

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_GermPointsNoConstantTermFirstZero
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.DerivEndo
variable {R : Type} [CommRing R] {d : ℕ}

theorem GlobalTheory.DerivEndo.ev_ev {l m n : ℕ} {a : Fin l → Pt R m d} {b : Fin m → Pt R n d} (hb : NoConst b)
    (ha : NoConst a) (f : PS R l d) :
    ev b (ev a f) = ev (fun j i => ev b (a j i)) f := by sorry
