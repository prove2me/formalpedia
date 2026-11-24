-- Prove2me | Theorems.Thm_GlobalTheory_padicNorm_of_sq_add_prime_mul_sq
-- name    : GlobalTheory.padicNorm_of_sq_add_prime_mul_sq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:12:57.725366+00:00
-- url     : https://prove2.me/theorems/0f3ccd95-c481-4f07-89a6-38ab6e93a48f
-- title:
--   Global Theory: padic Norm of sq add prime mul sq
-- statement:
--   The Global Theory construction uses the padic Norm of sq add prime mul sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SelfDualHermitianLatticeExistsNormOneMod.lean#L23-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SelfDualHermitianLatticeExistsNormOneMod.lean#L23-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SelfDualHermitianLatticeExistsNormOneMod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.padicNorm_of_sq_add_prime_mul_sq (p : ℕ) [hp : Fact p.Prime] (s t : ℚ)
    (h : padicNorm p (s ^ 2 + (p : ℚ) * t ^ 2) = 1) :
    padicNorm p s ≤ 1 ∧ padicNorm p ((p : ℚ) * t ^ 2) < 1 := by sorry
