-- Prove2me | Theorems.Thm_GlobalTheory_InvDiffLocal_mul_mem_of_trace_mem
-- name    : GlobalTheory.InvDiffLocal.mul_mem_of_trace_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:19:58.228353+00:00
-- url     : https://prove2.me/theorems/30a92e3f-8a8a-449f-b04d-316dd7842057
-- title:
--   Inv Diff Local: mul mem of trace mem
-- statement:
--   The Inv Diff Local construction uses the mul mem of trace mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ValuationMulLeOneOfTraceApproxIdempotentIntegral.lean#L56-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ValuationMulLeOneOfTraceApproxIdempotentIntegral.lean#L56-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ValuationMulLeOneOfTraceApproxIdempotentIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open Classical
open GlobalTheory GlobalTheory.InvDiffLocal

theorem GlobalTheory.InvDiffLocal.mul_mem_of_trace_mem {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (x : L)
    (hx : ∀ b : 𝓞 L, Algebra.trace K L ((b : L) * x) ∈ (algebraMap (𝓞 K) K).range) :
    ∀ d ∈ differentIdeal (𝓞 K) (𝓞 L), ∃ c : 𝓞 L, (c : L) = x * (d : L) := by sorry
