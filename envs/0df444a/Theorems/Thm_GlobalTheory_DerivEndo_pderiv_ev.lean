-- Prove2me | Theorems.Thm_GlobalTheory_DerivEndo_pderiv_ev
-- name    : GlobalTheory.DerivEndo.pderiv_ev
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:10:12.2688+00:00
-- url     : https://prove2.me/theorems/387b171e-0e6e-4e08-a544-9d45e2f0d07c
-- title:
--   Deriv Endo: pderiv ev
-- statement:
--   The Deriv Endo construction uses the pderiv ev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/GermPointsNoConstantTermFirstZero.lean#L102-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/GermPointsNoConstantTermFirstZero.lean#L102-L106

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

theorem GlobalTheory.DerivEndo.pderiv_ev {m n : ℕ} {a : Fin m → Pt R n d} (ha : NoConst a) (f : PS R m d)
    (v : Fin n × Fin d) :
    pderiv R v (ev a f) = ∑ j, ∑ i, ev a (pderiv R (j, i) f) * pderiv R v (a j i) := by sorry
