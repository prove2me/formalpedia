-- Prove2me | Theorems.Thm_GlobalTheory_IdemRange_ge_pow_mulVec
-- name    : GlobalTheory.IdemRange.ge_pow_mulVec
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-27T05:44:14.158276+00:00
-- url     : https://prove2.me/theorems/8663f48c-4995-5f87-b417-a53d2884ca54
-- title:
--   Idem Range: ge pow mul Vec
-- statement:
--   The Idem Range construction uses the ge pow mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LimitIdempotentRangeLeSumEigenspaces.lean#L108-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LimitIdempotentRangeLeSumEigenspaces.lean#L108-L112

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
import Theorems.Thm_ReciprocityTheory_PGsh_IsIntegralMat_mulVec

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
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem GlobalTheory.IdemRange.ge_pow_mulVec {M : Matrix κ κ C} (hM : ∀ i j, V.Ge 0 (M i j)) {v : κ → C} {w : ℝ}
    (hv : ∀ i, V.Ge w (v i)) (k : ℕ) : ∀ i, V.Ge w ((M ^ k).mulVec v i) := by sorry
