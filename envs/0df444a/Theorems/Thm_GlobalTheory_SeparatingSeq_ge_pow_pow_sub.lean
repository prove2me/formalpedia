-- Prove2me | Theorems.Thm_GlobalTheory_SeparatingSeq_ge_pow_pow_sub
-- name    : GlobalTheory.SeparatingSeq.ge_pow_pow_sub
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-27T06:18:33.192028+00:00
-- url     : https://prove2.me/theorems/f3d55a61-e2ad-4c28-b7f8-d59e3291733e
-- title:
--   Separating Seq: ge pow pow sub
-- statement:
--   The Separating Seq construction uses the ge pow pow sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsLadicSeparatingSequenceEmbeddings.lean#L25-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsLadicSeparatingSequenceEmbeddings.lean#L25-L37

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

theorem GlobalTheory.SeparatingSeq.ge_pow_pow_sub {t c : C} (ht : V.Ge 0 t) (hc : V.Ge 0 c) (h : V.Ge 1 (t - c)) (n : ℕ) :
    V.Ge n (t ^ V.l ^ n - c ^ V.l ^ n) := by sorry
