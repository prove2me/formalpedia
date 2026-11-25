-- Prove2me | Theorems.Thm_GlobalTheory_QuadDeriv_quad
-- name    : GlobalTheory.QuadDeriv.quad
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:04:09.92657+00:00
-- url     : https://prove2.me/theorems/ff014123-b9c2-485b-ab43-2dd8ebe9b792
-- title:
--   Quad Deriv: quad
-- statement:
--   The Quad Deriv construction uses the quad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalSecondPointDerivativeSecondCoordinate.lean#L288-L374
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalSecondPointDerivativeSecondCoordinate.lean#L288-L374

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

theorem GlobalTheory.QuadDeriv.quad (F : Fin d → PS k 2 d) (hF : GP F) (hU : evP (n := 1) ![pt k d 0, 0] F = pt k d 0)
    (w : Pt k 1 d) (hw : GP w)
    (hom : comp1 w F = addOf F (comp1 w (pt k (n := 2) d 0)) (comp1 w (pt k (n := 2) d 1)))
    (g : PS k 2 d) (h0 : ev (n := 1) ![0, pt k d 0] g = 0) (h1 : ev (n := 1) ![pt k d 0, 0] g = 0)
    (hl : ev (n := 3) ![pt k d 0, pt k d 2] g + ev (n := 3) ![pt k d 1, pt k d 2] g =
      ev (n := 3) ![addOf F (pt k d 0) (pt k d 1), pt k d 2] g)
    (hr : ev (n := 3) ![pt k d 0, pt k d 1] g + ev (n := 3) ![pt k d 0, pt k d 2] g =
      ev (n := 3) ![pt k d 0, addOf F (pt k d 1) (pt k d 2)] g) :
    constantCoeff (ev (n := 1) ![pt k d 0, w] g) = 0 ∧
    (∀ u, constantCoeff (Dof F u (ev (n := 1) ![pt k d 0, w] g)) = 0) ∧
    ∀ u v, Dof F u (Dof F v (ev (n := 1) ![pt k d 0, w] g)) =
      C (∑ j, (∑ l, v l * coeff (Finsupp.single ((0 : Fin 1), l) 1) (w j)) *
          (∑ i, u i * coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1) g) +
        ∑ i, v i * ∑ l, u l * ∑ j,
          coeff (Finsupp.single ((0 : Fin 2), i) 1 + Finsupp.single ((1 : Fin 2), j) 1) g *
            coeff (Finsupp.single ((0 : Fin 1), l) 1) (w j)) := by sorry
