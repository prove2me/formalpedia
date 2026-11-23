-- Prove2me | Theorems.Thm_GlobalTheory_AdditiveSeries_gp_pair
-- name    : GlobalTheory.AdditiveSeries.gp_pair
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:53:57.290324+00:00
-- url     : https://prove2.me/theorems/2385a577-634a-4852-ba3f-656605bd3b1f
-- title:
--   Additive Series: gp pair
-- statement:
--   The Additive Series construction uses the gp pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/EqZeroOfAdditiveOfPderiv.lean#L22-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/EqZeroOfAdditiveOfPderiv.lean#L22-L24

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

theorem GlobalTheory.AdditiveSeries.gp_pair {n : ℕ} {x y : Pt k n d} (hx : GP x) (hy : GP y) :
    ∀ j, GP ((![x, y] : Fin 2 → Pt k n d) j) := by sorry
