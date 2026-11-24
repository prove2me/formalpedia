-- Prove2me | Theorems.Thm_GlobalTheory_QuadDeriv_formalSecondPointDerivative_formalSubst_two
-- name    : GlobalTheory.QuadDeriv.formalSecondPointDerivative_formalSubst_two
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:08:13.762839+00:00
-- url     : https://prove2.me/theorems/955d651a-2f6d-41ed-96be-1e6f72d13ec0
-- title:
--   Quad Deriv: formal Second Point Derivative formal Subst two
-- statement:
--   The Quad Deriv construction uses the formal Second Point Derivative formal Subst two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalSecondPointDerivativeSecondCoordinate.lean#L99-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalSecondPointDerivativeSecondCoordinate.lean#L99-L106

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

theorem GlobalTheory.QuadDeriv.formalSecondPointDerivative_formalSubst_two (v : Fin d → k) (a b : Pt k 2 d) (ha : GP a) (hb : GP b) (f : PS k 2 d) :
    dy v (ev ![a, b] f) =
      ∑ i, dy v (a i) * ev ![evP (n := 1) ![pt k d 0, 0] a, evP (n := 1) ![pt k d 0, 0] b]
        (pderiv k ((0 : Fin 2), i) f) +
      ∑ i, dy v (b i) * ev ![evP (n := 1) ![pt k d 0, 0] a, evP (n := 1) ![pt k d 0, 0] b]
        (pderiv k ((1 : Fin 2), i) f) := by sorry
