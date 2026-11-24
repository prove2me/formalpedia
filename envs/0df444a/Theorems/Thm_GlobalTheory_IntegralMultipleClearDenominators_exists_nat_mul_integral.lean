-- Prove2me | Theorems.Thm_GlobalTheory_IntegralMultipleClearDenominators_exists_nat_mul_integral
-- name    : GlobalTheory.IntegralMultipleClearDenominators.exists_nat_mul_integral
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T17:20:49.975843+00:00
-- url     : https://prove2.me/theorems/e566948f-fcd7-4f3c-b0ec-44452a4c0b1e
-- title:
--   Integral Multiple Clear Denominators: exists nat mul integral
-- statement:
--   The Integral Multiple Clear Denominators construction uses the exists nat mul integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsNsmulMulVecMem.lean#L7-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsNsmulMulVecMem.lean#L7-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsNsmulMulVecMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntegralMultipleClearDenominators
open NumberField

theorem GlobalTheory.IntegralMultipleClearDenominators.exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ K : ℕ, 0 < K ∧ IsIntegral ℤ ((K : E) * c) := by sorry
