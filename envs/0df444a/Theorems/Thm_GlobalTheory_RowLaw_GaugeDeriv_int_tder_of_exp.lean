-- Prove2me | Theorems.Thm_GlobalTheory_RowLaw_GaugeDeriv_int_tder_of_exp
-- name    : GlobalTheory.RowLaw.GaugeDeriv.int_tder_of_exp
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-27T05:19:42.673816+00:00
-- url     : https://prove2.me/theorems/40b5e7b1-8b80-5229-ab5e-08884037e7f0
-- title:
--   Gauge Deriv: int tder of exp
-- statement:
--   The Gauge Deriv construction uses the int tder of exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GaugeDerivEqPairingOfIntegralGaugedLaw.lean#L198-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GaugeDerivEqPairingOfIntegralGaugedLaw.lean#L198-L204

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
variable [Fintype σ] {p : σ → MvPowerSeries τ C} (hp : ∀ s, constantCoeff (p s) = 0) (w : σ → MvPowerSeries τ C)
include hp

theorem GlobalTheory.RowLaw.GaugeDeriv.int_tder_of_exp [CharZero C] (hpi : ∀ s, IntS V (p s)) (hw : ∀ s, IntS V (w s)) {f : MvPowerSeries σ C}
    (hf0 : constantCoeff f = 0) (hf : IntS V (mvExp f)) (hz : subst p f = 0) : IntS V (tder p w f) := by sorry
