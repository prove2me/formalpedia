-- Prove2me | Theorems.Thm_GlobalTheory_RowLaw_CvEnd_intS_subst
-- name    : GlobalTheory.RowLaw.CvEnd.intS_subst
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-27T05:13:13.792314+00:00
-- url     : https://prove2.me/theorems/ba462d02-f4df-4d04-a2ef-37cef68dee23
-- title:
--   Cv End: int S subst
-- statement:
--   The Cv End construction uses the int S subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/AdjointEndPairMemGaugedCurveLogarithms.lean#L120-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/AdjointEndPairMemGaugedCurveLogarithms.lean#L120-L133

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_AdjointEndPairMemGaugedCurveLogarithms
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Van_subst

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
open GlobalTheory GlobalTheory.RowLaw GlobalTheory.RowLaw.CvEnd
open MvPowerSeries
variable {C : Type} [Field C]
variable {V : VF C} {σ τ : Type}

theorem GlobalTheory.RowLaw.CvEnd.intS_subst {a : σ → MvPowerSeries τ C} (ha : HasSubst a) (hi : ∀ s, IntS V (a s))
    {F : MvPowerSeries σ C} (hF : IntS V F) : IntS V (subst a F) := by sorry
