-- Prove2me | Theorems.Thm_GlobalTheory_RowLaw_AddCurve_subst_eq_zero_of_van
-- name    : GlobalTheory.RowLaw.AddCurve.subst_eq_zero_of_van
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-27T05:21:59.21387+00:00
-- url     : https://prove2.me/theorems/587a4126-b2e2-48c5-a570-0796aa7988fe
-- title:
--   Add Curve: subst eq zero of van
-- statement:
--   The Add Curve construction uses the subst eq zero of van property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/AddCurveStableOfIntegralGaugedFormalGroupLaw.lean#L58-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/AddCurveStableOfIntegralGaugedFormalGroupLaw.lean#L58-L64

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AddCurveStableOfIntegralGaugedFormalGroupLaw
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst

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
open Classical
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds MvPowerSeries
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.AddCurve
variable {C : Type} [Field C]

theorem GlobalTheory.RowLaw.AddCurve.subst_eq_zero_of_van {σ τ : Type} [Finite σ] {T : Set σ} {a : σ → MvPowerSeries τ C}
    (ha0 : ∀ s, constantCoeff (a s) = 0) (haT : ∀ s ∈ T, a s = 0) {f : MvPowerSeries σ C} (hf : Van T f) :
    subst a f = 0 := by sorry
