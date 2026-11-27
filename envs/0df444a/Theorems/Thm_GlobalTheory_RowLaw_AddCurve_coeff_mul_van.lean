-- Prove2me | Theorems.Thm_GlobalTheory_RowLaw_AddCurve_coeff_mul_van
-- name    : GlobalTheory.RowLaw.AddCurve.coeff_mul_van
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-27T05:14:51.528772+00:00
-- url     : https://prove2.me/theorems/95ae74eb-6a16-5a94-8fe2-4224c2e06b50
-- title:
--   Add Curve: coeff mul van
-- statement:
--   The Add Curve construction uses the coeff mul van property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/AddCurveStableOfIntegralGaugedFormalGroupLaw.lean#L66-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/AddCurveStableOfIntegralGaugedFormalGroupLaw.lean#L66-L101

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AddCurveStableOfIntegralGaugedFormalGroupLaw
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

theorem GlobalTheory.RowLaw.AddCurve.coeff_mul_van {τ : Type} {T : Set τ} {f g : MvPowerSeries τ C} (hf : Van T f) (hg : Van T g)
    (ν : τ →₀ ℕ) (hν : ∀ w ∈ ν.support, w ∉ T) (t : τ) : coeff (ν + Finsupp.single t 1) (f * g) = 0 := by sorry
