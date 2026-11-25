-- Prove2me | Theorems.Thm_GlobalTheory_InvDiffLocal_valuation_mul_different_le_one
-- name    : GlobalTheory.InvDiffLocal.valuation_mul_different_le_one
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:10:53.867797+00:00
-- url     : https://prove2.me/theorems/a96db1fe-95f8-4dfc-b2ff-8954cdf179d7
-- title:
--   Inv Diff Local: valuation mul different le one
-- statement:
--   The Inv Diff Local construction uses the valuation mul different le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ValuationMulLeOneOfTraceApproxIdempotentIntegral.lean#L117-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ValuationMulLeOneOfTraceApproxIdempotentIntegral.lean#L117-L183

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

theorem GlobalTheory.InvDiffLocal.valuation_mul_different_le_one : ∀ (K L : Type) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] (la : HeightOneSpectrum (𝓞 L)) (p : HeightOneSpectrum (𝓞 K)),
    la.asIdeal.under (𝓞 K) = p.asIdeal → ∀ y : L, (∃ N : ℕ, ∀ b : 𝓞 L,
      (∀ la' : HeightOneSpectrum (𝓞 L), la' ≠ la → la'.asIdeal.under (𝓞 K) = p.asIdeal →
        b ∈ la'.asIdeal ^ N) → p.valuation K (Algebra.trace K L ((b : L) * y)) ≤ 1) →
    ∀ d ∈ differentIdeal (𝓞 K) (𝓞 L), la.valuation L (y * (d : L)) ≤ 1 := by sorry
