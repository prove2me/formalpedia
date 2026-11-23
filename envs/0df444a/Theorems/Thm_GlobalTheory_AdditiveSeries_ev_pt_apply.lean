-- Prove2me | Theorems.Thm_GlobalTheory_AdditiveSeries_ev_pt_apply
-- name    : GlobalTheory.AdditiveSeries.ev_pt_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:53:43.579457+00:00
-- url     : https://prove2.me/theorems/71bc0958-0b1e-43b9-9794-10a6299a5c7f
-- title:
--   Additive Series: ev pt apply
-- statement:
--   The Additive Series construction uses the ev pt apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/EqZeroOfAdditiveOfPderiv.lean#L53-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/EqZeroOfAdditiveOfPderiv.lean#L53-L54

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

theorem GlobalTheory.AdditiveSeries.ev_pt_apply {m n : ℕ} {V : Fin m → Pt k n d} (hV : ∀ j, GP (V j)) (j : Fin m)
    (i : Fin d) : ev V (pt k d j i) = V j i := by sorry
