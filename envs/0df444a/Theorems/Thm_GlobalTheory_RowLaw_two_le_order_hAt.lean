-- Prove2me | Theorems.Thm_GlobalTheory_RowLaw_two_le_order_hAt
-- name    : GlobalTheory.RowLaw.two_le_order_hAt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-27T05:15:33.278669+00:00
-- url     : https://prove2.me/theorems/45fbb4d6-3a44-487d-8c2f-1ff19d57549f
-- title:
--   Row Law: two le order h At
-- statement:
--   The Row Law construction uses the two le order h At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/IntegralGaugeBilinearTermOfTypeNe.lean#L276-L288
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/IntegralGaugeBilinearTermOfTypeNe.lean#L276-L288

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntegralGaugeBilinearTermOfTypeNe
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
variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
variable {Y : RawChart C d I κ} {V : VF C}

theorem GlobalTheory.RowLaw.two_le_order_hAt (h : RLaw Y V) {τ : Type} {a b : κ → MvPowerSeries τ C}
    (ha : ∀ x, constantCoeff (a x) = 0) (hb : ∀ x, constantCoeff (b x) = 0) (e : τ →₀ ℕ)
    (he : e.degree < 2) : coeff e (hAt Y a b) = 0 := by sorry
