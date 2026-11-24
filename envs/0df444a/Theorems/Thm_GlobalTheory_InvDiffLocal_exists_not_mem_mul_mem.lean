-- Prove2me | Theorems.Thm_GlobalTheory_InvDiffLocal_exists_not_mem_mul_mem
-- name    : GlobalTheory.InvDiffLocal.exists_not_mem_mul_mem
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:19:59.442048+00:00
-- url     : https://prove2.me/theorems/6c0ca034-7bdc-4bbd-bddb-699210da4487
-- title:
--   Inv Diff Local: exists not mem mul mem
-- statement:
--   The Inv Diff Local construction uses the exists not mem mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ValuationMulLeOneOfTraceApproxIdempotentIntegral.lean#L9-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ValuationMulLeOneOfTraceApproxIdempotentIntegral.lean#L9-L50

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

theorem GlobalTheory.InvDiffLocal.exists_not_mem_mul_mem {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) (t : K)
    (ht : v.valuation K t ≤ 1) :
    ∃ s : R, s ∉ v.asIdeal ∧ ∃ r : R, algebraMap R K s * t = algebraMap R K r := by sorry
