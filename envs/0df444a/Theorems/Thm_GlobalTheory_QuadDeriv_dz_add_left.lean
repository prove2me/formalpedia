-- Prove2me | Theorems.Thm_GlobalTheory_QuadDeriv_dz_add_left
-- name    : GlobalTheory.QuadDeriv.dz_add_left
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:08:45.937793+00:00
-- url     : https://prove2.me/theorems/30b0e0a5-2e48-412d-b73c-feb056047a3d
-- title:
--   Quad Deriv: dz add left
-- statement:
--   The Quad Deriv construction uses the dz add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalSecondPointDerivativeSecondCoordinate.lean#L242-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalSecondPointDerivativeSecondCoordinate.lean#L242-L251

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

theorem GlobalTheory.QuadDeriv.dz_add_left
    (h : ev (n := 3) ![pt k d 0, pt k d 2] g + ev (n := 3) ![pt k d 1, pt k d 2] g =
      ev (n := 3) ![addOf F (pt k d 0) (pt k d 1), pt k d 2] g)
    (a b : Pt k 2 d) (ha : GP a) (hb : GP b) (i : Fin d) :
    ev ![addOf F a b, 0] (pderiv k ((1 : Fin 2), i) g) =
      ev ![a, 0] (pderiv k ((1 : Fin 2), i) g) + ev ![b, 0] (pderiv k ((1 : Fin 2), i) g) := by sorry
