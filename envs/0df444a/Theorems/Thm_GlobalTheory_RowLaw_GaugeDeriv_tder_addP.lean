-- Prove2me | Theorems.Thm_GlobalTheory_RowLaw_GaugeDeriv_tder_addP
-- name    : GlobalTheory.RowLaw.GaugeDeriv.tder_addP
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-27T05:17:06.699725+00:00
-- url     : https://prove2.me/theorems/e36c1336-f012-5812-8007-3177b51d56cc
-- title:
--   Gauge Deriv: tder add P
-- statement:
--   The Gauge Deriv construction uses the tder add P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GaugeDerivEqPairingOfIntegralGaugedLaw.lean#L437-L447
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GaugeDerivEqPairingOfIntegralGaugedLaw.lean#L437-L447

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
variable (R : RLaw Y V)
include R

theorem GlobalTheory.RowLaw.GaugeDeriv.tder_addP [Fintype τ] {a b : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0)
    (hb : ∀ i, constantCoeff (b i) = 0) {p : τ → MvPowerSeries υ C} (hp : ∀ s, constantCoeff (p s) = 0)
    (w : τ → MvPowerSeries υ C) (i : κ) :
    tder p w (addP Y a b i) =
      tder (fun x => subst (fun i => subst p (a i)) (Y.lg x) + subst (fun i => subst p (b i)) (Y.lg x))
        (fun x => tder (fun i => subst p (a i)) (fun i => tder p w (a i)) (Y.lg x) +
          tder (fun i => subst p (b i)) (fun i => tder p w (b i)) (Y.lg x)) (Y.ex i) := by sorry
