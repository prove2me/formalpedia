-- Prove2me | Theorems.Thm_GlobalTheory_discr_mul_isIntegral_of_traceDual
-- name    : GlobalTheory.discr_mul_isIntegral_of_traceDual
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:15:50.500223+00:00
-- url     : https://prove2.me/theorems/9e0c8ebe-908a-418a-b19b-88f6aa440fd5
-- title:
--   Global Theory: discr mul is Integral of trace Dual
-- statement:
--   The Global Theory construction uses the discr mul is Integral of trace Dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DiscriminantMulTraceDualIntegral.lean#L8-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DiscriminantMulTraceDualIntegral.lean#L8-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DiscriminantMulTraceDualIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open NumberField IsDedekindDomain
open scoped nonZeroDivisors

theorem GlobalTheory.discr_mul_isIntegral_of_traceDual :
    ∀ (K : Type) [Field K] [NumberField K] (x : K), (∀ y : 𝓞 K, ∃ n : ℤ, Algebra.trace ℚ K (x * y) = n) →
    IsIntegral ℤ ((discr K : K) * x) := by sorry
