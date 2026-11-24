-- Prove2me | Theorems.Thm_GlobalTheory_T_isReduced_of_nonZeroDivisor_mem_jacobson_of_assocPrimes
-- name    : GlobalTheory.T.isReduced_of_nonZeroDivisor_mem_jacobson_of_assocPrimes
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:49:35.395273+00:00
-- url     : https://prove2.me/theorems/cb7a80d4-9444-4f58-be19-ff0602eddde4
-- title:
--   T: is Reduced of non Zero Divisor mem jacobson of assoc Primes
-- statement:
--   The T construction uses the is Reduced of non Zero Divisor mem jacobson of assoc Primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsReducedOfNonZeroDivisorMemJacobsonOfAssociatedStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsReducedOfNonZeroDivisorMemJacobsonOfAssociatedStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsReducedOfNonZeroDivisorMemJacobsonOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsReducedOfNonZeroDivisorMemJacobsonOfAssociatedStatement
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

theorem GlobalTheory.T.isReduced_of_nonZeroDivisor_mem_jacobson_of_assocPrimes : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (x : R), x ∈ nonZeroDivisors R → x ∈ Ideal.jacobson (⊥ : Ideal R) → (∀ (P : Ideal R) [P.IsPrime], P ∈ associatedPrimes R (R ⧸ Ideal.span {x}) → IsDomain (Localization.AtPrime P)) → IsReduced R := by sorry
