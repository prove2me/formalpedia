-- Prove2me | Theorems.Thm_GlobalTheory_RowLaw_CvEnd_one_le_weightedOrder_expMulLog
-- name    : GlobalTheory.RowLaw.CvEnd.one_le_weightedOrder_expMulLog
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-27T05:11:43.411195+00:00
-- url     : https://prove2.me/theorems/6a111925-e322-45ec-93e1-571e6e0ef25c
-- title:
--   Cv End: one le weighted Order exp Mul Log
-- statement:
--   The Cv End construction uses the one le weighted Order exp Mul Log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/AdjointEndPairMemGaugedCurveLogarithms.lean#L297-L303
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/AdjointEndPairMemGaugedCurveLogarithms.lean#L297-L303

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AdjointEndPairMemGaugedCurveLogarithms
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

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
noncomputable section
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.CvEnd
open MvPowerSeries
variable {C : Type} [Field C]
variable {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] {X : RawChart C d I κ}

theorem GlobalTheory.RowLaw.CvEnd.one_le_weightedOrder_expMulLog (H : RLaw X V) (M : Matrix κ κ C) {τ : Type} {w : τ → ℕ} {b : κ → MvPowerSeries τ C}
    (hb : ∀ i, constantCoeff (b i) = 0) (hw : ∀ i, b i ∈ ordGe C w 1) (i : κ) :
    endP X M b i ∈ ordGe C w 1 := by sorry
