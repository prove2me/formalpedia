-- Prove2me | Theorems.Thm_GlobalTheory_QuadDeriv_add_right
-- name    : GlobalTheory.QuadDeriv.add_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:46:11.288682+00:00
-- url     : https://prove2.me/theorems/a0093ca7-a666-4895-959c-f5277363877d
-- title:
--   Quad Deriv: add right
-- statement:
--   The Quad Deriv construction uses the add right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalSecondPointDerivativeSecondCoordinate.lean#L172-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalSecondPointDerivativeSecondCoordinate.lean#L172-L184

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
variable (F : Fin d → PS k 2 d) (hF : GP F) (g : PS k 2 d)
include hF

theorem GlobalTheory.QuadDeriv.add_right
    (h : ev (n := 3) ![pt k d 0, pt k d 1] g + ev (n := 3) ![pt k d 0, pt k d 2] g =
      ev (n := 3) ![pt k d 0, addOf F (pt k d 1) (pt k d 2)] g)
    {n : ℕ} (a b c : Pt k n d) (ha : GP a) (hb : GP b) (hc : GP c) :
    ev ![a, addOf F b c] g = ev ![a, b] g + ev ![a, c] g := by sorry
