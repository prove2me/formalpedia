-- Prove2me | Theorems.Thm_GlobalTheory_associatedPrimes_subset_of_flat
-- name    : GlobalTheory.associatedPrimes_subset_of_flat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:50:27.362491+00:00
-- url     : https://prove2.me/theorems/b823ee48-185d-4e72-b56f-5b1f67fb3101
-- title:
--   Global Theory: associated Primes subset of flat
-- statement:
--   The Global Theory construction uses the associated Primes subset of flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasicOpenEqZeroOfMemIInfPowSmul.lean#L56-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasicOpenEqZeroOfMemIInfPowSmul.lean#L56-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasicOpenEqZeroOfMemIInfPowSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {M : Type*} [AddCommGroup M] [Module A M]

theorem GlobalTheory.associatedPrimes_subset_of_flat [IsNoetherianRing A] [Module.Flat A M] :
    associatedPrimes A M ⊆ associatedPrimes A A := by sorry
