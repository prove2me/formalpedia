-- Prove2me | Theorems.Thm_GlobalTheory_lowK_sub_single_and_sqrt_ckv_le
-- name    : GlobalTheory.lowK_sub_single_and_sqrt_ckv_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:02:29.358362+00:00
-- url     : https://prove2.me/theorems/8334d0de-0f6d-4695-af6b-b3e4e0a0daa7
-- title:
--   Global Theory: low K sub single and sqrt ckv le
-- statement:
--   The Global Theory construction uses the low K sub single and sqrt ckv le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/LowKSubSingleSqrtCkvLe.lean#L73-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/LowKSubSingleSqrtCkvLe.lean#L73-L117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_LowKSubSingleSqrtCkvLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
open GlobalTheory
open LowCasShift

theorem GlobalTheory.lowK_sub_single_and_sqrt_ckv_le :
    ∀ (n kk : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (bv : ℝ) (s : Fin n), Shape ε kk μ bv →
      lowK ε (μ - Pi.single s 1) = lowK ε μ - Pi.single s 1 ∧
      Real.sqrt (ckv ε (lowK ε μ)) + Real.sqrt n ≤
        Real.sqrt (ckv ε (lowK ε (μ - Pi.single s 1))) + 8 * n := by sorry
