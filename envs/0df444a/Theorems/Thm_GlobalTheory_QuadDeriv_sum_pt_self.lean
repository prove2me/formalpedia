-- Prove2me | Theorems.Thm_GlobalTheory_QuadDeriv_sum_pt_self
-- name    : GlobalTheory.QuadDeriv.sum_pt_self
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:06:26.363805+00:00
-- url     : https://prove2.me/theorems/dcc10171-63e4-4d8e-b137-8ae68dd94f67
-- title:
--   Quad Deriv: sum pt self
-- statement:
--   The Quad Deriv construction uses the sum pt self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalSecondPointDerivativeSecondCoordinate.lean#L209-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalSecondPointDerivativeSecondCoordinate.lean#L209-L215

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalSecondPointDerivativeSecondCoordinate
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
open GlobalTheory GlobalTheory.QuadDeriv
variable {k : Type} [CommRing k] {d : ℕ}

theorem GlobalTheory.QuadDeriv.sum_pt_self {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) (j : Fin m) (i : Fin d)
    (A : Fin d → PS k n d) : ∑ i', A i' * ev V (pderiv k (j, i) (pt k d j i')) = A i := by sorry
