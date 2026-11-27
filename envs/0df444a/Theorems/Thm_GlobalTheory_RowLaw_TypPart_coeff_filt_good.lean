-- Prove2me | Theorems.Thm_GlobalTheory_RowLaw_TypPart_coeff_filt_good
-- name    : GlobalTheory.RowLaw.TypPart.coeff_filt_good
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-27T06:15:27.292647+00:00
-- url     : https://prove2.me/theorems/897c679e-b50d-5a7e-836c-14a969034eda
-- title:
--   Typ Part: coeff filt good
-- statement:
--   The Typ Part construction uses the coeff filt good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PowExponentPartMemGaugedCurveLogarithms.lean#L109-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/PowExponentPartMemGaugedCurveLogarithms.lean#L109-L126

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

theorem GlobalTheory.RowLaw.TypPart.coeff_filt_good {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) (f : PowerSeries C) (m n : ℕ) (hn : m + 3 ≤ n) :
    PowerSeries.coeff m (filt (Good l n) f) = PowerSeries.coeff m (typ l f) := by sorry
