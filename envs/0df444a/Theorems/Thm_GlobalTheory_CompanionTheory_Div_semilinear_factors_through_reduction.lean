-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Div_semilinear_factors_through_reduction
-- name    : GlobalTheory.CompanionTheory.Div.semilinear_factors_through_reduction
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:00:26.100012+00:00
-- url     : https://prove2.me/theorems/efa3f5db-f660-5473-b21e-9f7a48338422
-- title:
--   Div: semilinear factors through reduction
-- statement:
--   The Div construction uses the semilinear factors through reduction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/DivisibilityProofs/SemilinearFactorsThroughReduction.lean#L5-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/DivisibilityProofs/SemilinearFactorsThroughReduction.lean#L5-L28

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_DivisibilityProofs_SemilinearFactorsThroughReduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Div

theorem GlobalTheory.CompanionTheory.Div.semilinear_factors_through_reduction :
    ∀ (A O : Type) [CommRing A] [CommRing O] (θ : A →+* O), Function.Surjective θ →
      ∀ (ξ : A), θ ξ = 0 →
      ∀ (M D L : Type) [AddCommGroup M] [Module A M] [AddCommGroup D] [Module O D]
        [AddCommGroup L] [Module O L] (r : M →ₛₗ[θ] D) (q : M →ₛₗ[θ] L),
        Function.Surjective r → (∀ m, r m = 0 ↔ ∃ n, m = ξ • n) →
        ∃ π : D →ₗ[O] L, ∀ m, π (r m) = q m := by sorry
