-- Prove2me | Theorems.Thm_GlobalTheory_RowLaw_GoodPair_coeff_mul_lead
-- name    : GlobalTheory.RowLaw.GoodPair.coeff_mul_lead
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-27T06:03:49.538398+00:00
-- url     : https://prove2.me/theorems/55e3d83a-ba9d-4d15-ac4e-b6c417a1ed18
-- title:
--   Good Pair: coeff mul lead
-- statement:
--   The Good Pair construction uses the coeff mul lead property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GoodCurvesPairingMemMaxIdeal.lean#L139-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GoodCurvesPairingMemMaxIdeal.lean#L139-L158

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AddCurveStableOfIntegralGaugedFormalGroupLaw
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AdjointEndPairMemGaugedCurveLogarithms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FrobeniusMemTypicalCurveSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntSOfMulEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GoodCurvesPairingMemMaxIdeal
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
open Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw GlobalTheory.RowLaw.CvEnd GlobalTheory.RowVal MvPowerSeries
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.GoodPair
variable {C : Type} [Field C]
variable {τ : Type} {V : VF C}

theorem GlobalTheory.RowLaw.GoodPair.coeff_mul_lead {F G : MvPowerSeries (Fin 2) C} {a b a' b' : ℕ} (hF : F ∈ ordGe C (wv 0) a)
    (hF' : F ∈ ordGe C (wv 1) b) (hG : G ∈ ordGe C (wv 0) a') (hG' : G ∈ ordGe C (wv 1) b') :
    coeff (ee (a + a') (b + b')) (F * G) = coeff (ee a b) F * coeff (ee a' b') G := by sorry
