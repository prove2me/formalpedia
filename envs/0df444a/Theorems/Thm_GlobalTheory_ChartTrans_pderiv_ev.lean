-- Prove2me | Theorems.Thm_GlobalTheory_ChartTrans_pderiv_ev
-- name    : GlobalTheory.ChartTrans.pderiv_ev
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:41:07.45863+00:00
-- url     : https://prove2.me/theorems/40c9d949-383a-4e24-9c71-328f1d97d9a3
-- title:
--   Chart Trans: pderiv ev
-- statement:
--   The Chart Trans construction uses the pderiv ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/AxisPderivComp.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/AxisPderivComp.lean#L18-L22

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_AxisPderivComp
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
open GlobalTheory GlobalTheory.ChartTrans
variable {k : Type} [CommRing k] {d : ℕ}

theorem GlobalTheory.ChartTrans.pderiv_ev {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) (f : PS k m d)
    (v : Fin n × Fin d) :
    pderiv k v (ev V f) = ∑ j : Fin m, ∑ l : Fin d, ev V (pderiv k (j, l) f) * pderiv k v (V j l) := by sorry
