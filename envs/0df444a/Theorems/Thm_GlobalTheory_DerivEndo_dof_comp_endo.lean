-- Prove2me | Theorems.Thm_GlobalTheory_DerivEndo_dof_comp_endo
-- name    : GlobalTheory.DerivEndo.dof_comp_endo
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T02:40:43.206017+00:00
-- url     : https://prove2.me/theorems/096d6a81-bf78-435c-9bec-6bd902e472c5
-- title:
--   Deriv Endo: dof comp endo
-- statement:
--   The Deriv Endo construction uses the dof comp endo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/GermPointsNoConstantTermFirstZero.lean#L261-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/GermPointsNoConstantTermFirstZero.lean#L261-L286

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

theorem GlobalTheory.DerivEndo.dof_comp_endo : ∀ (R : Type) [CommRing R] (d : ℕ) (G : FGLaw R d) (φ : Pt R 1 d),
    (∀ i, constantCoeff (φ i) = 0) →
    comp1 φ (G.add (pt R (n := 2) d 0) (pt R (n := 2) d 1)) =
      G.add (comp1 φ (pt R (n := 2) d 0)) (comp1 φ (pt R (n := 2) d 1)) →
    ∀ (u : Fin d → R) (f : PS R 1 d),
      Dof G.F u (ev (n := 1) ![φ] f) = ev (n := 1) ![φ] (Dof G.F ((dLin φ).mulVec u) f) := by sorry
