-- Prove2me | Theorems.Thm_GlobalTheory_RowLaw_GaugeDeriv_exists_sum
-- name    : GlobalTheory.RowLaw.GaugeDeriv.exists_sum
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-27T05:19:24.696415+00:00
-- url     : https://prove2.me/theorems/5c2bfd32-4893-4989-bb01-9c529be4b62e
-- title:
--   Gauge Deriv: exists sum
-- statement:
--   The Gauge Deriv construction uses the exists sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GaugeDerivEqPairingOfIntegralGaugedLaw.lean#L608-L625
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GaugeDerivEqPairingOfIntegralGaugedLaw.lean#L608-L625

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogChain
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugeDerivEqPairingOfIntegralGaugedLaw
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
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds MvPowerSeries
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.GaugeDeriv
variable {C : Type} [Field C] {V : VF C} {σ τ υ : Type}
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] {Y : RawChart C d I κ}

theorem GlobalTheory.RowLaw.GaugeDeriv.exists_sum (R : RLaw Y V) {ι : Type} (s : Finset ι) (b : ι → κ → MvPowerSeries τ C)
    (hb : ∀ c i, constantCoeff (b c i) = 0) (hbi : ∀ c i, IntS V (b c i)) :
    ∃ P : κ → MvPowerSeries τ C, (∀ i, constantCoeff (P i) = 0) ∧ (∀ i, IntS V (P i)) ∧
      (∀ x, subst P (Y.lg x) = ∑ c ∈ s, subst (b c) (Y.lg x)) ∧
      ∀ v : κ → C, (∀ i, V.Ge 0 (v i)) → IntS V (subst P (Y.sg v) - ∑ c ∈ s, subst (b c) (Y.sg v)) := by sorry
