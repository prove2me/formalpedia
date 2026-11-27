-- Prove2me | Theorems.Thm_GlobalTheory_TeichSeq_ge_pow_sub
-- name    : GlobalTheory.TeichSeq.ge_pow_sub
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-27T05:12:32.282396+00:00
-- url     : https://prove2.me/theorems/8c13619b-72df-5682-8a05-17b4dd472e8c
-- title:
--   Teich Seq: ge pow sub
-- statement:
--   The Teich Seq construction uses the ge pow sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FrobeniusLiftEmbeddingsUnit.lean#L129-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/FrobeniusLiftEmbeddingsUnit.lean#L129-L132

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EqOfMapEqOfPowEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FrobeniusLiftEmbeddingsUnit
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
open GlobalTheory GlobalTheory.TeichSeq
variable {C : Type} [Field C] (V : VF C)

theorem GlobalTheory.TeichSeq.ge_pow_sub {u w : C} (hu : V.Ge 0 u) (hw : V.Ge 0 w) {t : ℝ} (h : V.Ge t (u - w)) (m : ℕ) :
    V.Ge t (u ^ m - w ^ m) := by sorry
