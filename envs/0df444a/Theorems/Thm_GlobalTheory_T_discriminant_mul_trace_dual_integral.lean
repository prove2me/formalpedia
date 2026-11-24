-- Prove2me | Theorems.Thm_GlobalTheory_T_discriminant_mul_trace_dual_integral
-- name    : GlobalTheory.T.discriminant_mul_trace_dual_integral
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:32:46.10678+00:00
-- url     : https://prove2.me/theorems/5a8410e2-5792-4d48-af9e-b9fa77b64c52
-- title:
--   T: discriminant mul trace dual integral
-- statement:
--   The T construction uses the discriminant mul trace dual integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DiscriminantMulTraceDualIntegralStatement.lean#L6-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DiscriminantMulTraceDualIntegralStatement.lean#L6-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DiscriminantMulTraceDualIntegral
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DiscriminantMulTraceDualIntegralStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.discriminant_mul_trace_dual_integral : ∀ (K : Type) [Field K] [NumberField K] (x : K), (∀ y : 𝓞 K, ∃ n : ℤ, Algebra.trace ℚ K (x * y) = n) →
    IsIntegral ℤ ((discr K : K) * x) := by sorry
