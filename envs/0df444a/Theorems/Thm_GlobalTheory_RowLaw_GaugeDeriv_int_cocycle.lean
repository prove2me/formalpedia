-- Prove2me | Theorems.Thm_GlobalTheory_RowLaw_GaugeDeriv_int_cocycle
-- name    : GlobalTheory.RowLaw.GaugeDeriv.int_cocycle
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-27T05:19:24.931831+00:00
-- url     : https://prove2.me/theorems/6856c482-be78-59ad-9090-b16f5b9673c2
-- title:
--   Gauge Deriv: int cocycle
-- statement:
--   The Gauge Deriv construction uses the int cocycle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GaugeDerivEqPairingOfIntegralGaugedLaw.lean#L462-L497
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GaugeDerivEqPairingOfIntegralGaugedLaw.lean#L462-L497

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
variable {a b : κ → MvPowerSeries τ C} (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0)
  (hai : ∀ i, IntS V (a i)) (hbi : ∀ i, IntS V (b i))
include ha hb hai hbi
variable {v : κ → C} (hv : ∀ i, V.Ge 0 (v i))
include hv

theorem GlobalTheory.RowLaw.GaugeDeriv.int_cocycle : IntS V (subst (addP Y a b) (Y.sg v) - subst a (Y.sg v) - subst b (Y.sg v)) := by sorry
