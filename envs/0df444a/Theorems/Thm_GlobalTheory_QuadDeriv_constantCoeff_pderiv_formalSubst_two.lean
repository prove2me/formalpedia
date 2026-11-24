-- Prove2me | Theorems.Thm_GlobalTheory_QuadDeriv_constantCoeff_pderiv_formalSubst_two
-- name    : GlobalTheory.QuadDeriv.constantCoeff_pderiv_formalSubst_two
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:08:22.929565+00:00
-- url     : https://prove2.me/theorems/7c2dbf99-075f-4f36-bfcd-fe80e2d44be6
-- title:
--   Quad Deriv: constant Coeff pderiv formal Subst two
-- statement:
--   The Quad Deriv construction uses the constant Coeff pderiv formal Subst two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalSecondPointDerivativeSecondCoordinate.lean#L280-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/FormalSecondPointDerivativeSecondCoordinate.lean#L280-L286

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

theorem GlobalTheory.QuadDeriv.constantCoeff_pderiv_formalSubst_two (b c : Pt k 1 d) (hb : GP b) (hc : GP c) (f : PS k 2 d) (l : Fin d) :
    constantCoeff (pderiv k ((0 : Fin 1), l) (ev ![b, c] f)) =
      ∑ i, constantCoeff (pderiv k ((0 : Fin 2), i) f) * constantCoeff (pderiv k ((0 : Fin 1), l) (b i)) +
      ∑ i, constantCoeff (pderiv k ((1 : Fin 2), i) f) * constantCoeff (pderiv k ((0 : Fin 1), l) (c i)) := by sorry
