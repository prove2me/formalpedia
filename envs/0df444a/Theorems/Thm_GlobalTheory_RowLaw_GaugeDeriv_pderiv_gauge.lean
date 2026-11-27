-- Prove2me | Theorems.Thm_GlobalTheory_RowLaw_GaugeDeriv_pderiv_gauge
-- name    : GlobalTheory.RowLaw.GaugeDeriv.pderiv_gauge
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-27T05:19:18.931801+00:00
-- url     : https://prove2.me/theorems/9c284899-d09d-5016-b1e1-621631388d65
-- title:
--   Gauge Deriv: pderiv gauge
-- statement:
--   The Gauge Deriv construction uses the pderiv gauge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GaugeDerivEqPairingOfIntegralGaugedLaw.lean#L834-L860
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GaugeDerivEqPairingOfIntegralGaugedLaw.lean#L834-L860

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

theorem GlobalTheory.RowLaw.GaugeDeriv.pderiv_gauge (R : RLaw Y V) {Θ : WV I → MvPowerSeries (WV I) C} (hΘ0 : ∀ w, constantCoeff (Θ w) = 0)
    {P : Fin 2 → κ → MvPowerSeries (WV I) C} (h0 : ∀ g i, constantCoeff (P g i) = 0) (hi : ∀ g i, IntS V (P g i))
    (hP : ∀ g i, subst Θ (P g i) = Y.expPt g i) {g g' : Fin 2} (hg : g ≠ g') (k : I g') :
    ∃ J, IntS V J ∧ pderiv C (⟨g', k⟩ : WV I) (subst (fun p : Fin 2 × κ => Y.expPt p.1 p.2) Y.h) =
      subst Θ J - subst Θ (subst (P g) (Y.sg (Y.u g' k))) := by sorry
