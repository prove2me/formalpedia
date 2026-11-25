-- Prove2me | Theorems.Thm_GlobalTheory_DerivEndo_germ_ev_restrict_axis_groupLaw
-- name    : GlobalTheory.DerivEndo.germ_ev_restrict_axis_groupLaw
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:10:48.731858+00:00
-- url     : https://prove2.me/theorems/d592a32e-f9e5-4657-abc6-085ef50de974
-- title:
--   Deriv Endo: germ ev restrict axis group Law
-- statement:
--   The Deriv Endo construction uses the germ ev restrict axis group Law property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/GermPointsNoConstantTermFirstZero.lean#L170-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/GermPointsNoConstantTermFirstZero.lean#L170-L177

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

theorem GlobalTheory.DerivEndo.germ_ev_restrict_axis_groupLaw (G : FGLaw R d) (h : PS R 1 d) :
    ev (n := 1) ![pt R d 0, 0] (ev (n := 2) ![G.F] h) = h := by sorry
