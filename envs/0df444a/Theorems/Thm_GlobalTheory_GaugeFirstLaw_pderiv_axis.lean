-- Prove2me | Theorems.Thm_GlobalTheory_GaugeFirstLaw_pderiv_axis
-- name    : GlobalTheory.GaugeFirstLaw.pderiv_axis
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:49:09.591303+00:00
-- url     : https://prove2.me/theorems/a69c3362-a68a-40f5-b996-83cb418787a5
-- title:
--   Gauge First Law: pderiv axis
-- statement:
--   The Gauge First Law construction uses the pderiv axis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsGaugeFirstLaw.lean#L30-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsGaugeFirstLaw.lean#L30-L40

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_AxisPderivComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGaugeFirstLaw
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
open GlobalTheory GlobalTheory.GaugeFirstLaw
variable {k : Type} [CommRing k] {d : ℕ}

theorem GlobalTheory.GaugeFirstLaw.pderiv_axis (h : PS k 2 d) (i : Fin d) :
    pderiv k ((0 : Fin 1), i) (ev (n := 1) ![pt k d 0, 0] h) =
      ev (n := 1) ![pt k d 0, 0] (pderiv k ((0 : Fin 2), i) h) := by sorry
