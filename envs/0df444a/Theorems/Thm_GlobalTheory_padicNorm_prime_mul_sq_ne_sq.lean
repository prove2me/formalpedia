-- Prove2me | Theorems.Thm_GlobalTheory_padicNorm_prime_mul_sq_ne_sq
-- name    : GlobalTheory.padicNorm_prime_mul_sq_ne_sq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:12:56.541978+00:00
-- url     : https://prove2.me/theorems/c339ab7f-08b6-4883-9c55-2ad3aa956a4b
-- title:
--   Global Theory: padic Norm prime mul sq ne sq
-- statement:
--   The Global Theory construction uses the padic Norm prime mul sq ne sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SelfDualHermitianLatticeExistsNormOneMod.lean#L5-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SelfDualHermitianLatticeExistsNormOneMod.lean#L5-L21

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

theorem GlobalTheory.padicNorm_prime_mul_sq_ne_sq (p : ℕ) [hp : Fact p.Prime] (s t : ℚ) (ht : t ≠ 0) :
    padicNorm p (s ^ 2) ≠ padicNorm p ((p : ℚ) * t ^ 2) := by sorry
