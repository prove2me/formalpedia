-- Prove2me | Theorems.Thm_GlobalTheory_RowLaw_GaugeDeriv_group_point
-- name    : GlobalTheory.RowLaw.GaugeDeriv.group_point
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-27T05:21:21.948602+00:00
-- url     : https://prove2.me/theorems/f1803e58-9d01-51ea-89a3-a7c557235a64
-- title:
--   Gauge Deriv: group point
-- statement:
--   The Gauge Deriv construction uses the group point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GaugeDerivEqPairingOfIntegralGaugedLaw.lean#L696-L775
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GaugeDerivEqPairingOfIntegralGaugedLaw.lean#L696-L775

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_LogChain
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugeDerivEqPairingOfIntegralGaugedLaw
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
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds MvPowerSeries
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.GaugeDeriv
variable {C : Type} [Field C] {V : VF C} {σ τ υ : Type}
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] {Y : RawChart C d I κ}

theorem GlobalTheory.RowLaw.GaugeDeriv.group_point (R : RLaw Y V) {g : Fin 2} {H : Y.CartHyp V g} (S : Sys (RawChart.cart H))
    {t : I g → MvPowerSeries (I g) C} (ht : S.IsT t) {Θ : WV I → MvPowerSeries (WV I) C}
    (hΘ0 : ∀ w, constantCoeff (Θ w) = 0) (hΘ : ∀ c, Θ ⟨g, c⟩ = upG g (t c)) :
    ∃ P : κ → MvPowerSeries (WV I) C, (∀ i, constantCoeff (P i) = 0) ∧ (∀ i, IntS V (P i)) ∧
      (∀ i, subst Θ (P i) = Y.expPt g i) ∧
      ∀ q : JJ I g, ∃ J, IntS V J ∧ subst Θ (subst P (Y.sg (Y.u (1 - g) q))) = subst Θ J + upG g (S.ze t q) +
        ∑ y : I g, (if Y.ty g y = Y.ty (1 - g) q then Y.sg1 (Y.u g y) (Y.u (1 - g) q) else 0) •
          (X (⟨g, y⟩ : WV I) : MvPowerSeries (WV I) C) := by sorry
