-- Prove2me | Theorems.Thm_GlobalTheory_RowVal_EndCalc_constantCoeff_expMulLog
-- name    : GlobalTheory.RowVal.EndCalc.constantCoeff_expMulLog
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-27T05:59:30.45105+00:00
-- url     : https://prove2.me/theorems/21dfc1a2-21ce-5a43-a23f-98bc597d1365
-- title:
--   End Calc: constant Coeff exp Mul Log
-- statement:
--   The End Calc construction uses the constant Coeff exp Mul Log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GaugeBiadditiveSymmAdjointIntegralEnd.lean#L50-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GaugeBiadditiveSymmAdjointIntegralEnd.lean#L50-L53

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAxes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntSOfMulEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugeBiadditiveSymmAdjointIntegralEnd
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.RowVal GlobalTheory.RowVal.EndCalc
open MvPowerSeries
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
  {X : RawChart C d I κ}

theorem GlobalTheory.RowVal.EndCalc.constantCoeff_expMulLog (H : RLaw X V) {τ : Type} {a : κ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0)
    (A : Matrix κ κ C) (i : κ) : constantCoeff (endP X A a i) = 0 := by sorry
