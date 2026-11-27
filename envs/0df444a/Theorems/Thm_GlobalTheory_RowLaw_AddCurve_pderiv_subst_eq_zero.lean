-- Prove2me | Theorems.Thm_GlobalTheory_RowLaw_AddCurve_pderiv_subst_eq_zero
-- name    : GlobalTheory.RowLaw.AddCurve.pderiv_subst_eq_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-27T05:11:24.376335+00:00
-- url     : https://prove2.me/theorems/eeeee96b-fd89-546f-8861-83d2404e6d35
-- title:
--   Add Curve: pderiv subst eq zero
-- statement:
--   The Add Curve construction uses the pderiv subst eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/AddCurveStableOfIntegralGaugedFormalGroupLaw.lean#L229-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/AddCurveStableOfIntegralGaugedFormalGroupLaw.lean#L229-L233

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
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

theorem GlobalTheory.RowLaw.AddCurve.pderiv_subst_eq_zero {σ τ : Type} [Fintype σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) {t : τ} (h : ∀ s, pderiv C t (a s) = 0) (f : MvPowerSeries σ C) :
    pderiv C t (subst a f) = 0 := by sorry
