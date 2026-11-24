-- Prove2me | Theorems.Thm_GlobalTheory_SchwartzFstOp_norm_pow_mul_seminorm_sliceCLM_le
-- name    : GlobalTheory.SchwartzFstOp.norm_pow_mul_seminorm_sliceCLM_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:47:51.676958+00:00
-- url     : https://prove2.me/theorems/e53ac9a8-5214-4aac-9940-64cf0fb12fb4
-- title:
--   Schwartz Fst Op: norm pow mul seminorm slice CLM le
-- statement:
--   The Schwartz Fst Op construction uses the norm pow mul seminorm slice CLM le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzSliceSeminormLe.lean#L24-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzSliceSeminormLe.lean#L24-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthProdMkConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSliceSeminormLe
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
open GlobalTheory GlobalTheory.SchwartzFstOp

theorem GlobalTheory.SchwartzFstOp.norm_pow_mul_seminorm_sliceCLM_le {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup V'] [NormedSpace ℝ V'] (f : 𝓢(V × V', ℂ)) (x' : V') (j k n : ℕ) :
    ‖x'‖ ^ k * SchwartzMap.seminorm ℂ j n (sliceCLM x' f) ≤ SchwartzMap.seminorm ℂ (j + k) n f := by sorry
