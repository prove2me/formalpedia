-- Prove2me | Theorems.Thm_GlobalTheory_ActionLimit_low_ev_sub
-- name    : GlobalTheory.ActionLimit.low_ev_sub
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-27T05:16:22.910356+00:00
-- url     : https://prove2.me/theorems/cc6ad8e4-079d-5b7c-b254-be98147ab846
-- title:
--   Action Limit: low ev sub
-- statement:
--   The Action Limit construction uses the low ev sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ActionConvergesLadicCauchyAndStar.lean#L183-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ActionConvergesLadicCauchyAndStar.lean#L183-L188

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ConstantCoeffEv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ActionConvergesLadicCauchyAndStar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.ActionLimit
open MvPowerSeries GlobalTheory.GaugeAdjoint
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  (Y : FBChart C V O dd)
omit [CharZero C]

theorem GlobalTheory.ActionLimit.low_ev_sub {D m n : ℕ} {w c : ℝ} {x y : Fin m → Pt C n dd} {f : PS C m dd}
    (hx : ∀ j i, constantCoeff (x j i) = 0) (hy : ∀ j i, constantCoeff (y j i) = 0)
    (h : ∀ j i, Cong V D w (x j i) (y j i)) (hf : Low V D c f) :
    Low V D (c + w) (ev x f - ev y f) := by sorry
