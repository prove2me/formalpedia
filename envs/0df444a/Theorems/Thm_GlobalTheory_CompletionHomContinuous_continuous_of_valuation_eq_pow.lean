-- Prove2me | Theorems.Thm_GlobalTheory_CompletionHomContinuous_continuous_of_valuation_eq_pow
-- name    : GlobalTheory.CompletionHomContinuous.continuous_of_valuation_eq_pow
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:25:18.228862+00:00
-- url     : https://prove2.me/theorems/ade44882-3400-4834-ad39-3381d191f3e8
-- title:
--   Completion Hom Continuous: continuous of valuation eq pow
-- statement:
--   The Completion Hom Continuous construction uses the continuous of valuation eq pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ContinuousOfValuationEqPow.lean#L8-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ContinuousOfValuationEqPow.lean#L8-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ContinuousOfValuationEqPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Filter Topology
open scoped WithZeroTopology WithZero
open GlobalTheory GlobalTheory.CompletionHomContinuous

theorem GlobalTheory.CompletionHomContinuous.continuous_of_valuation_eq_pow {A B Γ : Type*} [Field A] [Field B]
    [LinearOrderedCommGroupWithZero Γ] [hA : Valued A Γ] [hB : Valued B Γ]
    (hs : Function.Surjective hA.v) (g : A →+* B) {e : ℕ} (he : 0 < e)
    (hg : ∀ x, hB.v (g x) = hA.v x ^ e) : Continuous g := by sorry
