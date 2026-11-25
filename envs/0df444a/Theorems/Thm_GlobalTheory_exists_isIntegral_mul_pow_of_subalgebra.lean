-- Prove2me | Theorems.Thm_GlobalTheory_exists_isIntegral_mul_pow_of_subalgebra
-- name    : GlobalTheory.exists_isIntegral_mul_pow_of_subalgebra
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:03:49.00729+00:00
-- url     : https://prove2.me/theorems/dd6a6af0-d1aa-5f52-a7e8-b35c986313d4
-- title:
--   Global Theory: exists is Integral mul pow of subalgebra
-- statement:
--   The Global Theory construction uses the exists is Integral mul pow of subalgebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsIsIntegralMulPowOfSubalgebra.lean#L102-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsIsIntegralMulPowOfSubalgebra.lean#L102-L142

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIsIntegralMulPowOfSubalgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Polynomial
variable {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {J : Type*}

theorem GlobalTheory.exists_isIntegral_mul_pow_of_subalgebra (A B : Subalgebra o Ω) {u : Ω} (hu : u ∈ B)
    (hr : ∀ r ∈ A, ∃ n : ℕ, r * u ^ n ∈ B) {z : Ω} (hz : IsIntegral A z) :
    ∃ N : ℕ, ∀ M, N ≤ M → IsIntegral B (z * u ^ M) := by sorry
