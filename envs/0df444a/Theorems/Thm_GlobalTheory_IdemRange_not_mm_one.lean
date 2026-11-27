-- Prove2me | Theorems.Thm_GlobalTheory_IdemRange_not_mm_one
-- name    : GlobalTheory.IdemRange.not_mm_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-27T05:44:19.137907+00:00
-- url     : https://prove2.me/theorems/4e53adb1-fe4d-56f1-ad0e-82c94e235966
-- title:
--   Idem Range: not mm one
-- statement:
--   The Idem Range construction uses the not mm one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LimitIdempotentRangeLeSumEigenspaces.lean#L40-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LimitIdempotentRangeLeSumEigenspaces.lean#L40-L41

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

theorem GlobalTheory.IdemRange.not_mm_one : ¬ V.MM (1 : C) := by sorry
