-- Prove2me | Theorems.Thm_GlobalTheory_RowVal_EndCalc_end_calc
-- name    : GlobalTheory.RowVal.EndCalc.end_calc
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-27T06:04:52.67051+00:00
-- url     : https://prove2.me/theorems/8b56ccca-cd91-43af-b063-c8e71d63c02e
-- title:
--   End Calc: end calc
-- statement:
--   The End Calc construction uses the end calc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GaugeBiadditiveSymmAdjointIntegralEnd.lean#L239-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GaugeBiadditiveSymmAdjointIntegralEnd.lean#L239-L272

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
variable [CharZero C]

theorem GlobalTheory.RowVal.EndCalc.end_calc : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → IntEnd X V 0 ∧ (∀ A B, IntEnd X V A → IntEnd X V B → IntEnd X V (A + B)) ∧ (∀ A B, IntEnd X V A → IntEnd X V B → IntEnd X V (A * B)) ∧ (∀ A, hEnd X A 0 = 0 ∧ hEnd X 0 A = 0) ∧ (∀ A A' B, IntEnd X V A → IntEnd X V A' → IntEnd X V B → hEnd X A B + hEnd X A' B - hEnd X (A + A') B ∈ logInt V κ ∧ hEnd X B A + hEnd X B A' - hEnd X B (A + A') ∈ logInt V κ) ∧ (∀ A B, IntEnd X V A → IntEnd X V B → hEnd X B A - hEnd X A B ∈ logInt V κ) ∧ (∀ M M' A B, IsEnd X V M M' → IntEnd X V A → IntEnd X V B → hEnd X (M * A) B - hEnd X A (M' * B) ∈ logInt V κ) := by sorry
