-- Prove2me | Theorems.Thm_GlobalTheory_AdditiveSeries_ev_ev_cons
-- name    : GlobalTheory.AdditiveSeries.ev_ev_cons
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:53:22.226828+00:00
-- url     : https://prove2.me/theorems/b626cfad-3ff6-499e-9e4b-36878ee350c7
-- title:
--   Additive Series: ev ev cons
-- statement:
--   The Additive Series construction uses the ev ev cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/EqZeroOfAdditiveOfPderiv.lean#L44-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/EqZeroOfAdditiveOfPderiv.lean#L44-L51

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalLogEqSumOfMultiplicativeParam
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_EqZeroOfAdditiveOfPderiv
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
open GlobalTheory GlobalTheory.AdditiveSeries
variable {k : Type} [CommRing k] {d : ℕ}

theorem GlobalTheory.AdditiveSeries.ev_ev_cons {l m n : ℕ} {V : Fin m → Pt k n d} (hV : ∀ j, GP (V j)) {x : Pt k m d}
    {y : Fin l → Pt k m d} (hx : GP x) (hy : ∀ j, GP (y j)) (g : PS k (l + 1) d) :
    ev V (ev (Fin.cons x y) g) =
      ev (Fin.cons (fun i => ev V (x i)) fun j i => ev V (y j i)) g := by sorry
