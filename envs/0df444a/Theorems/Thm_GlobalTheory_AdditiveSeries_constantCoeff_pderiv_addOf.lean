-- Prove2me | Theorems.Thm_GlobalTheory_AdditiveSeries_constantCoeff_pderiv_addOf
-- name    : GlobalTheory.AdditiveSeries.constantCoeff_pderiv_addOf
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:53:25.744601+00:00
-- url     : https://prove2.me/theorems/515826d7-b751-40b0-aed3-f46ce7f27e07
-- title:
--   Additive Series: constant Coeff pderiv add Of
-- statement:
--   The Additive Series construction uses the constant Coeff pderiv add Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/EqZeroOfAdditiveOfPderiv.lean#L91-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/EqZeroOfAdditiveOfPderiv.lean#L91-L104

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

theorem GlobalTheory.AdditiveSeries.constantCoeff_pderiv_addOf {q : ℕ} (G : FGLaw k d) (i l : Fin d) :
    constantCoeff (pderiv k ((0 : Fin (q + 2)), i)
      (addOf G.F (pt k d (0 : Fin (q + 2))) (pt k d 1) l)) = if l = i then 1 else 0 := by sorry
