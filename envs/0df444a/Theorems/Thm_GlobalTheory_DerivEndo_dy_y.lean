-- Prove2me | Theorems.Thm_GlobalTheory_DerivEndo_dy_y
-- name    : GlobalTheory.DerivEndo.dy_y
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:10:38.391222+00:00
-- url     : https://prove2.me/theorems/eec9e956-bab0-493e-acc2-8e3e9a88f3c0
-- title:
--   Deriv Endo: dy y
-- statement:
--   The Deriv Endo construction uses the dy y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/GermPointsNoConstantTermFirstZero.lean#L188-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/GermPointsNoConstantTermFirstZero.lean#L188-L199

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

theorem GlobalTheory.DerivEndo.dy_y (h : PS R 1 d) (i : Fin d) :
    pderiv R ((1 : Fin 2), i) (ev (n := 2) ![pt R d 1] h) =
      ev (n := 2) ![pt R d 1] (pderiv R ((0 : Fin 1), i) h) := by sorry
