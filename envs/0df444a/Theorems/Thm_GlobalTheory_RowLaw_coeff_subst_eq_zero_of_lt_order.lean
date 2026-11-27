-- Prove2me | Theorems.Thm_GlobalTheory_RowLaw_coeff_subst_eq_zero_of_lt_order
-- name    : GlobalTheory.RowLaw.coeff_subst_eq_zero_of_lt_order
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-27T05:04:40.68995+00:00
-- url     : https://prove2.me/theorems/ec37e738-5d20-58f6-9fc7-3d91710b9b90
-- title:
--   Row Law: coeff subst eq zero of lt order
-- statement:
--   The Row Law construction uses the coeff subst eq zero of lt order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/IntegralGaugeBilinearTermOfTypeNe.lean#L19-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/IntegralGaugeBilinearTermOfTypeNe.lean#L19-L27

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntegralGaugeBilinearTermOfTypeNe
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
open GlobalTheory GlobalTheory.RowLaw
variable {C : Type} [Field C]

theorem GlobalTheory.RowLaw.coeff_subst_eq_zero_of_lt_order {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, constantCoeff (a s) = 0) {f : MvPowerSeries σ C} {n : ℕ}
    (hf : ∀ e : σ →₀ ℕ, e.degree < n → coeff e f = 0) :
    (n : ℕ∞) ≤ (subst a f).order := by sorry
