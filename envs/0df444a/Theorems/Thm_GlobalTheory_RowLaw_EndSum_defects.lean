-- Prove2me | Theorems.Thm_GlobalTheory_RowLaw_EndSum_defects
-- name    : GlobalTheory.RowLaw.EndSum.defects
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-27T06:01:13.66809+00:00
-- url     : https://prove2.me/theorems/2f8fa8ad-92b9-54b4-8964-5ea8373eb10f
-- title:
--   End Sum: defects
-- statement:
--   The End Sum construction uses the defects property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/IsGaugeAdjointIntegralEndPairAdd.lean#L128-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/IsGaugeAdjointIntegralEndPairAdd.lean#L128-L159

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

theorem GlobalTheory.RowLaw.EndSum.defects [CharZero C] (h : RLaw X V) {τ : Type} {a b c : κ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) (hb : ∀ s, constantCoeff (b s) = 0) (hc : ∀ s, constantCoeff (c s) = 0)
    (hai : ∀ s, IntS V (a s)) (hbi : ∀ s, IntS V (b s)) (hci : ∀ s, IntS V (c s)) :
    hAt X a c + hAt X b c - hAt X (addP X a b) c ∈ logInt V τ ∧
      hAt X a b + hAt X a c - hAt X a (addP X b c) ∈ logInt V τ := by sorry
