-- Prove2me | Theorems.Thm_GlobalTheory_T_lowK_sub_single_sqrt_ckv_le
-- name    : GlobalTheory.T.lowK_sub_single_sqrt_ckv_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:36:34.409699+00:00
-- url     : https://prove2.me/theorems/4b9c09ab-59e7-5242-ab42-e88c7257d476
-- title:
--   T: low K sub single sqrt ckv le
-- statement:
--   The T construction uses the low K sub single sqrt ckv le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/LowKSubSingleSqrtCkvLeStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/LowKSubSingleSqrtCkvLeStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_LowKSubSingleSqrtCkvLe
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_LowKSubSingleSqrtCkvLeStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.lowK_sub_single_sqrt_ckv_le : ∀ (n kk : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (bv : ℝ) (s : Fin n), Shape ε kk μ bv → lowK ε (μ - Pi.single s 1) = lowK ε μ - Pi.single s 1 ∧ Real.sqrt (ckv ε (lowK ε μ)) + Real.sqrt n ≤ Real.sqrt (ckv ε (lowK ε (μ - Pi.single s 1))) + 8 * n := by sorry
