-- Prove2me | Theorems.Thm_GlobalTheory_CanonGaugeAssembly_const_of_ax
-- name    : GlobalTheory.CanonGaugeAssembly.const_of_ax
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:07:14.655717+00:00
-- url     : https://prove2.me/theorems/c2904f34-cb52-4178-8cd5-4ed8916063f6
-- title:
--   Canon Gauge Assembly: const of ax
-- statement:
--   The Canon Gauge Assembly construction uses the const of ax property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/CanonGaugeOfSteps.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/CanonGaugeOfSteps.lean#L18-L21

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_NabTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonGaugeOfSteps
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
open GlobalTheory GlobalTheory.CanonGaugeAssembly
variable {k : Type} [CommRing k] {d : ℕ}

theorem GlobalTheory.CanonGaugeAssembly.const_of_ax {h : PS k 2 d} (h0 : ev (n := 1) ![0, pt k d 0] h = 0) :
    constantCoeff h = 0 := by sorry
