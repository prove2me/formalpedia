-- Prove2me | Theorems.Thm_GlobalTheory_exists_isDiscreteValuationRing_of_mem_associatedPrimes_quotient
-- name    : GlobalTheory.exists_isDiscreteValuationRing_of_mem_associatedPrimes_quotient
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:33:16.242717+00:00
-- url     : https://prove2.me/theorems/c384d130-0ccc-4ac5-9c05-0709c46c5a34
-- title:
--   Global Theory: exists is Discrete Valuation Ring of mem associated Primes quotient
-- statement:
--   The Global Theory construction uses the exists is Discrete Valuation Ring of mem associated Primes quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AssociatedPrimeLocalizationDvr.lean#L83-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AssociatedPrimeLocalizationDvr.lean#L83-L198

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

theorem GlobalTheory.exists_isDiscreteValuationRing_of_mem_associatedPrimes_quotient :
    ∀ (A R : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [CommRing R] [IsNoetherianRing R] [Algebra A R] [Module.Flat A R] (x : A), x ≠ 0 →
      (∀ q : Ideal A, q.IsPrime → x ∈ q → IsReduced (R ⧸ q.map (algebraMap A R))) →
      ∀ (P : Ideal R) [P.IsPrime], P ∈ associatedPrimes R (R ⧸ Ideal.span {algebraMap A R x}) →
        ∃ _ : IsDomain (Localization.AtPrime P), IsDiscreteValuationRing (Localization.AtPrime P) := by sorry
