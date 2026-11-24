-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_glOnto_zero_and_glCount_zero
-- name    : GlobalTheory.PMonE.glOnto_zero_and_glCount_zero
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:39:49.069798+00:00
-- url     : https://prove2.me/theorems/4d377d6a-6691-439c-8564-6b96b44b28c6
-- title:
--   PMon E: gl Onto zero and gl Count zero
-- statement:
--   The PMon E construction uses the gl Onto zero and gl Count zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemSurjectivityAndCountOrderZero.lean#L7-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemSurjectivityAndCountOrderZero.lean#L7-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUniqueIntegralAdditiveSystemFrobeniusPower
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemSurjectivityAndCountOrderZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PMonE

theorem GlobalTheory.PMonE.glOnto_zero_and_glCount_zero : GLOnto 0 ∧ GLCount 0 := by sorry
