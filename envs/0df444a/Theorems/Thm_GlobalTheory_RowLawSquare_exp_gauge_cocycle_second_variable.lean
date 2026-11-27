-- Prove2me | Theorems.Thm_GlobalTheory_RowLawSquare_exp_gauge_cocycle_second_variable
-- name    : GlobalTheory.RowLawSquare.exp_gauge_cocycle_second_variable
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-27T05:24:04.337396+00:00
-- url     : https://prove2.me/theorems/5778c316-a310-4d66-a6bf-520afd982a4b
-- title:
--   Row Law Square: exp gauge cocycle second variable
-- statement:
--   The Row Law Square construction uses the exp gauge cocycle second variable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/IsIntegralGaugedFormalGroupLawSelfConjugateSquar.lean#L288-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/IsIntegralGaugedFormalGroupLawSelfConjugateSquar.lean#L288-L300

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IsIntegralGaugedFormalGroupLawSelfConjugateSquar
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst

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
open scoped BigOperators
open MvPowerSeries Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.RowLawSquare
variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  (Y : FBChart C V O dd) {τ : Type}

theorem GlobalTheory.RowLawSquare.exp_gauge_cocycle_second_variable {a b c : Fin dd → MvPowerSeries τ C} (ha : Zc a) (hb : Zc b) (hc : Zc c) :
    PowerSeries.subst (sb ![a, b] Y.h + sb ![a, c] Y.h - sb ![a, law Y b c] Y.h) (PowerSeries.exp C) =
      sb ![a, b, c] Y.B.ph2 := by sorry
