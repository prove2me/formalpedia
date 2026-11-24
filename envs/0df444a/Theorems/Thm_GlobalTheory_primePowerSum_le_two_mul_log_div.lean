-- Prove2me | Theorems.Thm_GlobalTheory_primePowerSum_le_two_mul_log_div
-- name    : GlobalTheory.primePowerSum_le_two_mul_log_div
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:15:36.368905+00:00
-- url     : https://prove2.me/theorems/1586f853-323f-40e0-b070-d03c4db5e96f
-- title:
--   Global Theory: prime Power Sum le two mul log div
-- statement:
--   The Global Theory construction uses the prime Power Sum le two mul log div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/GeomIccOneLeTwoMulSub.lean#L18-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/GeomIccOneLeTwoMulSub.lean#L18-L52

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeomIccOneLeTwoMulSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open GlobalTheory

theorem GlobalTheory.primePowerSum_le_two_mul_log_div (x : ℝ) (hx : 0 < x) (p : ℕ) (hp : p.Prime) :
    Formalism.HermitianLattices.GL2a2.sP x p ≤ 2 * x * Real.log p / p := by sorry
