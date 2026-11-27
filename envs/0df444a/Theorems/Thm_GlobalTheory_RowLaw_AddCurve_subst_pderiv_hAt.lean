-- Prove2me | Theorems.Thm_GlobalTheory_RowLaw_AddCurve_subst_pderiv_hAt
-- name    : GlobalTheory.RowLaw.AddCurve.subst_pderiv_hAt
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-27T05:15:38.819625+00:00
-- url     : https://prove2.me/theorems/2dc3e572-d41f-5a4f-bde4-e18eaa9ee065
-- title:
--   Add Curve: subst pderiv h At
-- statement:
--   The Add Curve construction uses the subst pderiv h At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/AddCurveStableOfIntegralGaugedFormalGroupLaw.lean#L192-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/AddCurveStableOfIntegralGaugedFormalGroupLaw.lean#L192-L227

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AddCurveStableOfIntegralGaugedFormalGroupLaw
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
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

theorem GlobalTheory.RowLaw.AddCurve.subst_pderiv_hAt (X : RawChart C d I κ) {τ : Type} {A : κ → MvPowerSeries (Fin 3 × κ) C}
    (hA : ∀ s, constantCoeff (A s) = 0) (i : κ) (hA' : ∀ x, pderiv C ((2 : Fin 3), i) (A x) = 0)
    {a : Fin 3 × κ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0) (ha2 : ∀ x, a (2, x) = 0) :
    subst a (pderiv C ((2 : Fin 3), i) (hAt X A (gp C κ 2))) =
      subst (fun p : Fin 2 × κ => if p.1 = 0 then subst a (A p.2) else 0) (pderiv C ((1 : Fin 2), i) X.h) := by sorry
