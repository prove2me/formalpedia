-- Prove2me | Theorems.Thm_GlobalTheory_exists_under_eq_of_mem_associatedPrimes_of_surjective
-- name    : GlobalTheory.exists_under_eq_of_mem_associatedPrimes_of_surjective
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:46:00.125269+00:00
-- url     : https://prove2.me/theorems/2d2e358d-7f4d-4fca-b819-2a9529834f08
-- title:
--   Global Theory: exists under eq of mem associated Primes of surjective
-- statement:
--   The Global Theory construction uses the exists under eq of mem associated Primes of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AssociatedPrimeLocalizationDvr.lean#L9-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AssociatedPrimeLocalizationDvr.lean#L9-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasicOpenEqZeroOfMemIInfPowSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AssociatedPrimeLocalizationDvr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory

theorem GlobalTheory.exists_under_eq_of_mem_associatedPrimes_of_surjective {A A' M : Type*} [CommRing A]
    [CommRing A'] [Algebra A A'] [AddCommGroup M] [Module A M] [Module A' M]
    [IsScalarTower A A' M] (hs : Function.Surjective (algebraMap A A')) {q : Ideal A}
    (hq : q ∈ associatedPrimes A M) : ∃ q' ∈ associatedPrimes A' M, q'.under A = q := by sorry
