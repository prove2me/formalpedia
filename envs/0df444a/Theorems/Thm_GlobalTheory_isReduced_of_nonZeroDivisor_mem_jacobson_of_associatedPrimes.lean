-- Prove2me | Theorems.Thm_GlobalTheory_isReduced_of_nonZeroDivisor_mem_jacobson_of_associatedPrimes
-- name    : GlobalTheory.isReduced_of_nonZeroDivisor_mem_jacobson_of_associatedPrimes
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:00:02.836656+00:00
-- url     : https://prove2.me/theorems/dcd457b6-55c6-4c4a-b283-d934bea4cf2b
-- title:
--   Global Theory: is Reduced of non Zero Divisor mem jacobson of associated Primes
-- statement:
--   The Global Theory construction uses the is Reduced of non Zero Divisor mem jacobson of associated Primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsReducedOfNonZeroDivisorMemJacobsonOfAssociated.lean#L28-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsReducedOfNonZeroDivisorMemJacobsonOfAssociated.lean#L28-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsReducedOfNonZeroDivisorMemJacobsonOfAssociated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory

theorem GlobalTheory.isReduced_of_nonZeroDivisor_mem_jacobson_of_associatedPrimes :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (x : R), x ∈ nonZeroDivisors R →
      x ∈ Ideal.jacobson (⊥ : Ideal R) →
      (∀ (P : Ideal R) [P.IsPrime], P ∈ associatedPrimes R (R ⧸ Ideal.span {x}) →
        IsDomain (Localization.AtPrime P)) → IsReduced R := by sorry
