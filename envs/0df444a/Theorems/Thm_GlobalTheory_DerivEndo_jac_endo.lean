-- Prove2me | Theorems.Thm_GlobalTheory_DerivEndo_jac_endo
-- name    : GlobalTheory.DerivEndo.jac_endo
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:10:05.646326+00:00
-- url     : https://prove2.me/theorems/5a454e1e-2b32-45ca-a46b-e74435123b1d
-- title:
--   Deriv Endo: jac endo
-- statement:
--   The Deriv Endo construction uses the jac endo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/GermPointsNoConstantTermFirstZero.lean#L231-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/GermPointsNoConstantTermFirstZero.lean#L231-L254

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_FourierCoeffIntSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_GermPointsNoConstantTermFirstZero
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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.DerivEndo
variable {R : Type} [CommRing R] {d : ℕ}

theorem GlobalTheory.DerivEndo.jac_endo (G : FGLaw R d) (φ : Pt R 1 d) (hφ : ∀ i, constantCoeff (φ i) = 0)
    (hom : comp1 φ (G.add (pt R (n := 2) d 0) (pt R (n := 2) d 1)) =
      G.add (comp1 φ (pt R (n := 2) d 0)) (comp1 φ (pt R (n := 2) d 1))) (a i : Fin d) :
    ∑ c, pderiv R ((0 : Fin 1), c) (φ a) *
        ev (n := 1) ![pt R d 0, 0] (pderiv R ((1 : Fin 2), i) (G.F c)) =
      ∑ b, ev (n := 1) ![φ] (ev (n := 1) ![pt R d 0, 0] (pderiv R ((1 : Fin 2), b) (G.F a))) *
        C (dLin φ b i) := by sorry
