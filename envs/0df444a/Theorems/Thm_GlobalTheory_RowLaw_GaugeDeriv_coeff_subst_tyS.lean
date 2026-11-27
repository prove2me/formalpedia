-- Prove2me | Theorems.Thm_GlobalTheory_RowLaw_GaugeDeriv_coeff_subst_tyS
-- name    : GlobalTheory.RowLaw.GaugeDeriv.coeff_subst_tyS
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-27T05:24:20.615497+00:00
-- url     : https://prove2.me/theorems/e985e544-d02b-4bcb-a3ec-295f0d410ba7
-- title:
--   Gauge Deriv: coeff subst ty S
-- statement:
--   The Gauge Deriv construction uses the coeff subst ty S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GaugeDerivEqPairingOfIntegralGaugedLaw.lean#L627-L655
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GaugeDerivEqPairingOfIntegralGaugedLaw.lean#L627-L655

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

theorem GlobalTheory.RowLaw.GaugeDeriv.coeff_subst_tyS {l : ℕ} (hl : 2 ≤ l) {a : MvPowerSeries τ C} (ha : constantCoeff a = 0) (x : ℕ → C)
    (μ : τ →₀ ℕ) : coeff μ (subst (fun _ : Unit => a) (tyS l x)) =
      ∑ s ∈ Finset.range (μ.degree + 1), x s * coeff μ (a ^ (l ^ s)) := by sorry
