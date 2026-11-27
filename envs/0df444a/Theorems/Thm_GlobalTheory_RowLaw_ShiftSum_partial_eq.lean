-- Prove2me | Theorems.Thm_GlobalTheory_RowLaw_ShiftSum_partial_eq
-- name    : GlobalTheory.RowLaw.ShiftSum.partial_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-27T05:48:46.87691+00:00
-- url     : https://prove2.me/theorems/b92b8db2-a14d-464d-bb2c-4cd428054f88
-- title:
--   Shift Sum: partial eq
-- statement:
--   The Shift Sum construction uses the partial eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ShiftedSumMemTypicalCurveSet.lean#L37-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ShiftedSumMemTypicalCurveSet.lean#L37-L46

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AddCurveStableOfIntegralGaugedFormalGroupLawStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugedCurveLogarithmsClosedUnderTadicLimitsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ShiftedSumMemTypicalCurveSet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.ShiftSum
variable {C : Type} [Field C]

theorem GlobalTheory.RowLaw.ShiftSum.partial_eq {N : Type} (y : ℕ → ℕ → N → C) (i M : ℕ) (hM : i < M) (n : N) :
    (∑ s ∈ Finset.range M, Vpow s (y s)) i n = sumV y i n := by sorry
