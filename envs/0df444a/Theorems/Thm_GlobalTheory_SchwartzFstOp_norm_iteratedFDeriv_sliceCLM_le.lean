-- Prove2me | Theorems.Thm_GlobalTheory_SchwartzFstOp_norm_iteratedFDeriv_sliceCLM_le
-- name    : GlobalTheory.SchwartzFstOp.norm_iteratedFDeriv_sliceCLM_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:48:03.376995+00:00
-- url     : https://prove2.me/theorems/5d08501d-e414-4673-8252-f6cb6f9fb75c
-- title:
--   Schwartz Fst Op: norm iterated FDeriv slice CLM le
-- statement:
--   The Schwartz Fst Op construction uses the norm iterated FDeriv slice CLM le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzSliceSeminormLe.lean#L8-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzSliceSeminormLe.lean#L8-L22

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

theorem GlobalTheory.SchwartzFstOp.norm_iteratedFDeriv_sliceCLM_le {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup V'] [NormedSpace ℝ V'] (f : 𝓢(V × V', ℂ)) (x' : V') (n : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ n (sliceCLM x' f) x‖ ≤ ‖iteratedFDeriv ℝ n f (x, x')‖ := by sorry
