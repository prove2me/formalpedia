-- Prove2me | Theorems.Thm_GlobalTheory_RowLaw_GoodPair_sc_int
-- name    : GlobalTheory.RowLaw.GoodPair.sc_int
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-27T05:59:58.004022+00:00
-- url     : https://prove2.me/theorems/cab86526-0c62-5c08-ad81-dc9e82c37dbb
-- title:
--   Good Pair: sc int
-- statement:
--   The Good Pair construction uses the sc int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GoodCurvesPairingMemMaxIdeal.lean#L364-L368
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GoodCurvesPairingMemMaxIdeal.lean#L364-L368

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
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

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
variable {V : VF C}

theorem GlobalTheory.RowLaw.GoodPair.sc_int (k : Fin 2) {z : C} (hz : V.Ge 0 z) (s : Fin 2) :
    IntS V ((sc k z • (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) C)) s) := by sorry
