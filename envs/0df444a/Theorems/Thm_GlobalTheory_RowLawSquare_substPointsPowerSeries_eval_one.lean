-- Prove2me | Theorems.Thm_GlobalTheory_RowLawSquare_substPointsPowerSeries_eval_one
-- name    : GlobalTheory.RowLawSquare.substPointsPowerSeries_eval_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-27T05:13:16.243268+00:00
-- url     : https://prove2.me/theorems/b2496607-670a-5e9b-8be4-5cce80a31cb6
-- title:
--   Row Law Square: subst Points Power Series eval one
-- statement:
--   The Row Law Square construction uses the subst Points Power Series eval one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/IsIntegralGaugedFormalGroupLawSelfConjugateSquar.lean#L144-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/IsIntegralGaugedFormalGroupLawSelfConjugateSquar.lean#L144-L151

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IsIntegralGaugedFormalGroupLawSelfConjugateSquar
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
variable {C : Type} [Field C] {σ τ : Type}
variable {dd : ℕ}

theorem GlobalTheory.RowLawSquare.substPointsPowerSeries_eval_one {n : ℕ} {a : Fin n → Fin dd → MvPowerSeries τ C} (ha : ∀ j, Zc (a j))
    {b : Pt C n dd} (hb : Zc b) (f : PS C 1 dd) :
    sb a (ev ![b] f) = sb ![fun i => sb a (b i)] f := by sorry
