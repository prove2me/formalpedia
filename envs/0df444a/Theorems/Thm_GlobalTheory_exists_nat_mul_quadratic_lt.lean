-- Prove2me | Theorems.Thm_GlobalTheory_exists_nat_mul_quadratic_lt
-- name    : GlobalTheory.exists_nat_mul_quadratic_lt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:35:22.780869+00:00
-- url     : https://prove2.me/theorems/bcee2d17-5e32-4e8e-8122-a2ccd35c6256
-- title:
--   Global Theory: exists nat mul quadratic lt
-- statement:
--   The Global Theory construction uses the exists nat mul quadratic lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsNatMulQuadraticLt.lean#L7-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsNatMulQuadraticLt.lean#L7-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsNatMulQuadraticLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory

theorem GlobalTheory.exists_nat_mul_quadratic_lt (N : ℕ) (hN : 1 ≤ N) (a b q c : ℚ) (hq : q < 0) :
    ∃ k : ℕ, a + ((N : ℚ) * k) * b + ((N : ℚ) * k) ^ 2 * q < c := by sorry
