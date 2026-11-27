-- Prove2me | Theorems.Thm_GlobalTheory_RowLaw_GoodPair_core
-- name    : GlobalTheory.RowLaw.GoodPair.core
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-27T06:20:45.078842+00:00
-- url     : https://prove2.me/theorems/3d033c94-69af-4824-99c8-4b6d30a04a85
-- title:
--   Good Pair: core
-- statement:
--   The Good Pair construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GoodCurvesPairingMemMaxIdeal.lean#L568-L648
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GoodCurvesPairingMemMaxIdeal.lean#L568-L648

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AddCurveStableOfIntegralGaugedFormalGroupLaw
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AdjointEndPairMemGaugedCurveLogarithms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FrobeniusMemTypicalCurveSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntSOfMulEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GoodCurvesPairingMemMaxIdeal
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
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw GlobalTheory.RowLaw.CvEnd GlobalTheory.RowVal MvPowerSeries
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.GoodPair
variable {C : Type} [Field C]
variable {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] {X : RawChart C d I κ}

theorem GlobalTheory.RowLaw.GoodPair.core (H : RLaw X V) {γ γ' : κ → PowerSeries C} (hγ : IsCv V γ) (hγ' : IsCv V γ')
    (hA : ∀ i n, V.l ∣ n → n < V.l * V.l → PowerSeries.coeff n (alongCv γ (X.lg i)) = 0)
    (hB : ∀ i n, V.l ∣ n → n < V.l * V.l → PowerSeries.coeff n (alongCv γ' (X.lg i)) = 0)
    (hM : V.MM ((V.l : C) * ∑ j, ((V.l : C) * PowerSeries.coeff (V.l * V.l) (alongCv γ (X.lg j))) *
      PowerSeries.coeff V.l (alongCv γ' (dz j X.h)))) :
    V.MM ((V.l : C) * ∑ j, PowerSeries.coeff 1 (alongCv γ' (X.lg j)) *
      PowerSeries.coeff V.l (alongCv γ (dz j X.h))) := by sorry
