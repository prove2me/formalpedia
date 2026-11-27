-- Prove2me | Theorems.Thm_GlobalTheory_RowLaw_EndSum_subst_addP
-- name    : GlobalTheory.RowLaw.EndSum.subst_addP
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-27T05:59:30.72803+00:00
-- url     : https://prove2.me/theorems/fdcb0422-e173-59e7-bdf2-bc69f3200abf
-- title:
--   End Sum: subst add P
-- statement:
--   The End Sum construction uses the subst add P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/IsGaugeAdjointIntegralEndPairAdd.lean#L66-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/IsGaugeAdjointIntegralEndPairAdd.lean#L66-L76

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntSOfMulEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IsGaugeAdjointIntegralEndPairAdd
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
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw GlobalTheory.RowVal MvPowerSeries
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.EndSum
variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} {κ : Type} [Fintype κ]
  {X : RawChart C d I κ} {V : VF C}

theorem GlobalTheory.RowLaw.EndSum.subst_addP (h : RLaw X V) {τ ρ : Type} [Finite τ] {a b : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0)
    {c : τ → MvPowerSeries ρ C} (hc : ∀ s, constantCoeff (c s) = 0) (x : κ) :
    subst c (addP X a b x) = addP X (fun y => subst c (a y)) (fun y => subst c (b y)) x := by sorry
