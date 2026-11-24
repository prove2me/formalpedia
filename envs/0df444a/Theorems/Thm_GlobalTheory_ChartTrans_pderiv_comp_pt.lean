-- Prove2me | Theorems.Thm_GlobalTheory_ChartTrans_pderiv_comp_pt
-- name    : GlobalTheory.ChartTrans.pderiv_comp_pt
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:09:22.656797+00:00
-- url     : https://prove2.me/theorems/64eb73c3-dec4-4628-88db-dd189d6a8485
-- title:
--   Chart Trans: pderiv comp pt
-- statement:
--   The Chart Trans construction uses the pderiv comp pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/AxisPderivComp.lean#L74-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/AxisPderivComp.lean#L74-L88

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

theorem GlobalTheory.ChartTrans.pderiv_comp_pt (φ : Pt k 1 d) (a b : Fin 2) (i l : Fin d) :
    pderiv k (a, i) (comp1 φ (pt k (n := 2) d b) l) =
      if a = b then ev ![pt k (n := 2) d b] (pderiv k ((0 : Fin 1), i) (φ l)) else 0 := by sorry
