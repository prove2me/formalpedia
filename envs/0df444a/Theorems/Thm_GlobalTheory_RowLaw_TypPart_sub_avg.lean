-- Prove2me | Theorems.Thm_GlobalTheory_RowLaw_TypPart_sub_avg
-- name    : GlobalTheory.RowLaw.TypPart.sub_avg
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-27T06:16:54.992328+00:00
-- url     : https://prove2.me/theorems/44b9a754-f941-489f-8207-d317188130a9
-- title:
--   Typ Part: sub avg
-- statement:
--   The Typ Part construction uses the sub avg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PowExponentPartMemGaugedCurveLogarithms.lean#L82-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PowExponentPartMemGaugedCurveLogarithms.lean#L82-L91

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugedFormalGroupCurveLogarithmsAddSubgroupRescaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GaugedCurveLogarithmsClosedUnderTadicLimits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CurveLogarithmsInvNatCastSmulMemStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PowExponentPartMemGaugedCurveLogarithms
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
noncomputable section
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.TypPart
variable {C : Type} [Field C]

theorem GlobalTheory.RowLaw.TypPart.sub_avg [CharZero C] {ζ : C} {p : ℕ} (hp : 0 < p) (hζ : IsPrimitiveRoot ζ p) (f : PowerSeries C) :
    f + -((p : C)⁻¹ • ∑ j ∈ Finset.range p, PowerSeries.rescale (ζ ^ j) f) = filt (fun m => ¬ p ∣ m) f := by sorry
