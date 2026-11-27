-- Prove2me | Theorems.Thm_GlobalTheory_SeparatingSeq_ge_of_mul_unit
-- name    : GlobalTheory.SeparatingSeq.ge_of_mul_unit
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-27T05:55:26.761505+00:00
-- url     : https://prove2.me/theorems/c0d434c5-a977-5928-b193-a2fde5d8c254
-- title:
--   Separating Seq: ge of mul unit
-- statement:
--   The Separating Seq construction uses the ge of mul unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsLadicSeparatingSequenceEmbeddings.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsLadicSeparatingSequenceEmbeddings.lean#L19-L23

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IntSOfMulEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsEmbeddingCongrIntegralCharacter
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsLadicSeparatingSequenceEmbeddings
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.SeparatingSeq
open TeichSeq
variable {C : Type} [Field C] {V : VF C}

theorem GlobalTheory.SeparatingSeq.ge_of_mul_unit {w : ℝ} {a u : C} (hu : V.Ge 0 u) (hu' : ¬ V.MM u)
    (h : V.Ge w (a * u)) : V.Ge w a := by sorry
