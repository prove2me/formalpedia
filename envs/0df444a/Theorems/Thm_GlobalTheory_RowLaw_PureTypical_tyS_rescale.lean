-- Prove2me | Theorems.Thm_GlobalTheory_RowLaw_PureTypical_tyS_rescale
-- name    : GlobalTheory.RowLaw.PureTypical.tyS_rescale
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-27T06:26:11.375098+00:00
-- url     : https://prove2.me/theorems/a9a194e6-0934-4c1e-8d1d-5759558422e9
-- title:
--   Pure Typical: ty S rescale
-- statement:
--   The Pure Typical construction uses the ty S rescale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsPureTypicalCurveWithIntegralTangent.lean#L39-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsPureTypicalCurveWithIntegralTangent.lean#L39-L45

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugedFormalGroupCurveLogarithmsAddSubgroupRescaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CurveLogarithmsInvNatCastSmulMemStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PowExponentPartMemGaugedCurveLogarithmsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AdjointEndPairMemGaugedCurveLogarithmsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsPureTypicalCurveWithIntegralTangent
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
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.PureTypical
variable {C : Type} [Field C]

theorem GlobalTheory.RowLaw.PureTypical.tyS_rescale {l : ℕ} (hl : 2 ≤ l) (c : C) (a : ℕ → C) :
    tyS l (fun s => c ^ (l ^ s) * a s) = PowerSeries.rescale c (tyS l a) := by sorry
