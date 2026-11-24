-- Prove2me | Theorems.Thm_GlobalTheory_InvDiffLocal_exists_approx_idempotent
-- name    : GlobalTheory.InvDiffLocal.exists_approx_idempotent
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:20:04.149807+00:00
-- url     : https://prove2.me/theorems/d9ecf08a-10b9-4c37-91ac-953147c58756
-- title:
--   Inv Diff Local: exists approx idempotent
-- statement:
--   The Inv Diff Local construction uses the exists approx idempotent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ValuationMulLeOneOfTraceApproxIdempotentIntegral.lean#L81-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ValuationMulLeOneOfTraceApproxIdempotentIntegral.lean#L81-L109

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
open IsDedekindDomain.HeightOneSpectrum

theorem GlobalTheory.InvDiffLocal.exists_approx_idempotent {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (la : HeightOneSpectrum (𝓞 L)) (p : HeightOneSpectrum (𝓞 K)) (N : ℕ) :
    ∃ z : 𝓞 L, z ∉ la.asIdeal ∧ ∀ la' : HeightOneSpectrum (𝓞 L), la' ≠ la →
      la'.asIdeal.under (𝓞 K) = p.asIdeal → z ∈ la'.asIdeal ^ N := by sorry
