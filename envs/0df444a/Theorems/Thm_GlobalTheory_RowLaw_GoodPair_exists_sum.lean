-- Prove2me | Theorems.Thm_GlobalTheory_RowLaw_GoodPair_exists_sum
-- name    : GlobalTheory.RowLaw.GoodPair.exists_sum
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-27T06:04:31.782617+00:00
-- url     : https://prove2.me/theorems/1521575b-dc01-4573-8562-d2d9b3e82473
-- title:
--   Good Pair: exists sum
-- statement:
--   The Good Pair construction uses the exists sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GoodCurvesPairingMemMaxIdeal.lean#L450-L470
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GoodCurvesPairingMemMaxIdeal.lean#L450-L470

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
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw GlobalTheory.RowLaw.CvEnd GlobalTheory.RowVal MvPowerSeries
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.GoodPair
variable {C : Type} [Field C]
variable {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] {X : RawChart C d I κ}

theorem GlobalTheory.RowLaw.GoodPair.exists_sum [CharZero C] (H : RLaw X V) {τ : Type} {a : ℕ → κ → MvPowerSeries τ C} {b : κ → MvPowerSeries τ C}
    (ha : ∀ j i, constantCoeff (a j i) = 0) (hb : ∀ i, constantCoeff (b i) = 0)
    (hai : ∀ j i, IntS V (a j i)) (hbi : ∀ i, IntS V (b i)) (n : ℕ) :
    ∃ S : κ → MvPowerSeries τ C, (∀ i, constantCoeff (S i) = 0) ∧ (∀ i, IntS V (S i)) ∧
      (∀ i, subst S (X.lg i) = ∑ j ∈ Finset.range n, subst (a j) (X.lg i)) ∧
      ∑ j ∈ Finset.range n, hAt X (a j) b - hAt X S b ∈ logInt V τ := by sorry
