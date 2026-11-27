-- Prove2me | Theorems.Thm_GlobalTheory_RowLaw_RLaw_coeff_single_endP
-- name    : GlobalTheory.RowLaw.RLaw.coeff_single_endP
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-27T05:05:01.2656+00:00
-- url     : https://prove2.me/theorems/42848f0d-8743-5eb1-b62a-47aaa2322358
-- title:
--   RLaw: coeff single end P
-- statement:
--   The RLaw construction uses the coeff single end P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/IntegralGaugeBilinearTermOfTypeNe.lean#L245-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/IntegralGaugeBilinearTermOfTypeNe.lean#L245-L254

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

theorem GlobalTheory.RowLaw.RLaw.coeff_single_endP (h : RLaw Y V) (M : Matrix κ κ C) {τ : Type} {a : κ → MvPowerSeries τ C}
    (ha : ∀ x, constantCoeff (a x) = 0) (x : κ) (t : τ) :
    coeff (Finsupp.single t 1) (endP Y M a x) = ∑ y, M x y * coeff (Finsupp.single t 1) (a y) := by sorry
