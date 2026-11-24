-- Prove2me | Theorems.Thm_GlobalTheory_T_schwartz_slice_seminorm_le
-- name    : GlobalTheory.T.schwartz_slice_seminorm_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:57:41.836679+00:00
-- url     : https://prove2.me/theorems/aa32be33-7913-4132-9d85-6722d17aad40
-- title:
--   T: schwartz slice seminorm le
-- statement:
--   The T construction uses the schwartz slice seminorm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzSliceSeminormLeStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzSliceSeminormLeStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSliceSeminormLe
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthProdMkConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSliceSeminormLeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap ContDiff
open GlobalTheory.SchwartzFstOp
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.schwartz_slice_seminorm_le : ∀ {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V'] [NormedSpace ℝ V'] (f : 𝓢(V × V', ℂ)) (x' : V') (j k n : ℕ), ‖x'‖ ^ k * SchwartzMap.seminorm ℂ j n (sliceCLM x' f) ≤ SchwartzMap.seminorm ℂ (j + k) n f := by sorry
