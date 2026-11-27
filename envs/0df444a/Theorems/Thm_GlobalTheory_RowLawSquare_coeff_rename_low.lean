-- Prove2me | Theorems.Thm_GlobalTheory_RowLawSquare_coeff_rename_low
-- name    : GlobalTheory.RowLawSquare.coeff_rename_low
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-27T05:20:28.051153+00:00
-- url     : https://prove2.me/theorems/4957fb09-adbe-506a-98ec-eb17526013e3
-- title:
--   Row Law Square: coeff rename low
-- statement:
--   The Row Law Square construction uses the coeff rename low property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/IsIntegralGaugedFormalGroupLawSelfConjugateSquar.lean#L76-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/IsIntegralGaugedFormalGroupLawSelfConjugateSquar.lean#L76-L92

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IsIntegralGaugedFormalGroupLawSelfConjugateSquar
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
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MvPowerSeries Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.RowLawSquare
variable {C : Type} [Field C] {σ τ : Type}

theorem GlobalTheory.RowLawSquare.coeff_rename_low [Finite σ] (φ : σ → τ) {f g : MvPowerSeries σ C} {N : ℕ}
    (hfg : ∀ e : σ →₀ ℕ, e.degree ≤ N → coeff e f = coeff e g) (μ : τ →₀ ℕ) (hμ : μ.degree ≤ N) :
    coeff μ (subst (fun s => (X (φ s) : MvPowerSeries τ C)) f) =
      coeff μ (subst (fun s => (X (φ s) : MvPowerSeries τ C)) g) := by sorry
