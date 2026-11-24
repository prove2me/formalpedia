-- Prove2me | Theorems.Thm_GlobalTheory_T_isIntegrallyClosed_of_integral_mul_mem_of_assocPrimes
-- name    : GlobalTheory.T.isIntegrallyClosed_of_integral_mul_mem_of_assocPrimes
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T20:50:18.637844+00:00
-- url     : https://prove2.me/theorems/71b33bcc-a426-482e-bc6d-38ba077e58d2
-- title:
--   T: is Integrally Closed of integral mul mem of assoc Primes
-- statement:
--   The T construction uses the is Integrally Closed of integral mul mem of assoc Primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsIntegrallyClosedOfConductorNonZeroDivisorOfAssStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsIntegrallyClosedOfConductorNonZeroDivisorOfAssStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsIntegrallyClosedOfConductorNonZeroDivisorOfAss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsIntegrallyClosedOfConductorNonZeroDivisorOfAssStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isIntegrallyClosed_of_integral_mul_mem_of_assocPrimes : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (x : R), x ∈ nonZeroDivisors R → (∀ (P : Ideal R) [P.IsPrime], P ∈ associatedPrimes R (R ⧸ Ideal.span {x}) → ∃ _ : IsDomain (Localization.AtPrime P), IsIntegrallyClosed (Localization.AtPrime P)) → (∀ c : FractionRing R, IsIntegral R c → ∃ s : R, algebraMap R (FractionRing R) s = algebraMap R (FractionRing R) x * c) → IsIntegrallyClosed R := by sorry
