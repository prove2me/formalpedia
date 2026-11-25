-- Prove2me | Theorems.Thm_GlobalTheory_norm_map_pow_mul_pow_of_mul_conj
-- name    : GlobalTheory.norm_map_pow_mul_pow_of_mul_conj
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:12:37.445726+00:00
-- url     : https://prove2.me/theorems/b8369e4b-04d5-4c2a-ad95-dbf2778bcc41
-- title:
--   Global Theory: norm map pow mul pow of mul conj
-- statement:
--   The Global Theory construction uses the norm map pow mul pow of mul conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/LogNormMapPowMulPowOfMulConj.lean#L16-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/LogNormMapPowMulPowOfMulConj.lean#L16-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LogNormMapPowMulPowOfMulConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open GlobalTheory

theorem GlobalTheory.norm_map_pow_mul_pow_of_mul_conj {K : Type*} [Semiring K] (σ : K →+* ℂ) (x y : K) (g : ℕ)
    (hxy : x * y = g) (hy : σ y = starRingEnd ℂ (σ x)) (a b : ℕ) :
    ‖σ (x ^ a * y ^ b)‖ = (g : ℝ) ^ (((a : ℝ) + b) / 2) := by sorry
