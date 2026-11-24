-- Prove2me | Theorems.Thm_GlobalTheory_AdditiveSeries_pderiv_ev_cons
-- name    : GlobalTheory.AdditiveSeries.pderiv_ev_cons
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:58:59.568677+00:00
-- url     : https://prove2.me/theorems/3903c7a0-abf5-4b84-8daa-6585fdea7569
-- title:
--   Additive Series: pderiv ev cons
-- statement:
--   The Additive Series construction uses the pderiv ev cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/EqZeroOfAdditiveOfPderiv.lean#L33-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/EqZeroOfAdditiveOfPderiv.lean#L33-L42

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

theorem GlobalTheory.AdditiveSeries.pderiv_ev_cons {m n : ℕ} {x : Pt k n d} {y : Fin m → Pt k n d} (hx : GP x)
    (hy : ∀ j, GP (y j)) (v : Fin n × Fin d) (hv : ∀ j i, pderiv k v (y j i) = 0)
    (g : PS k (m + 1) d) :
    pderiv k v (ev (Fin.cons x y) g) =
      ∑ l, ev (Fin.cons x y) (pderiv k ((0 : Fin (m + 1)), l) g) * pderiv k v (x l) := by sorry
