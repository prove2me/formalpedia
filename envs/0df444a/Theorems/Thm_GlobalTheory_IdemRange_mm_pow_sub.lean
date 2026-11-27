-- Prove2me | Theorems.Thm_GlobalTheory_IdemRange_mm_pow_sub
-- name    : GlobalTheory.IdemRange.mm_pow_sub
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-27T05:50:40.907972+00:00
-- url     : https://prove2.me/theorems/159fb7de-ee5b-5ee8-ac37-019089ef9da3
-- title:
--   Idem Range: mm pow sub
-- statement:
--   The Idem Range construction uses the mm pow sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LimitIdempotentRangeLeSumEigenspaces.lean#L46-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LimitIdempotentRangeLeSumEigenspaces.lean#L46-L53

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NondegenerateCharts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieSelf
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockAdmissibleChart
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NegMem
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_HasTeich
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsEmbeddingCongrIntegralCharacterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RingHomEqOfCongruentIntegralUnramifiedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EigenvectorOfGeneralizedEigenUnramifiedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsIntegralCharacterGeneralizedEigenStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LimitIdempotentRangeLeSumEigenspaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Formalism.L2.FormalSeriesBounds
open GlobalTheory GlobalTheory.IdemRange
variable {C : Type} [Field C] {V : VF C}

theorem GlobalTheory.IdemRange.mm_pow_sub {a b : C} (h : V.MM (a - b)) (ha : V.Ge 0 a) (hb : V.Ge 0 b) (n : ℕ) :
    V.MM (a ^ n - b ^ n) := by sorry
