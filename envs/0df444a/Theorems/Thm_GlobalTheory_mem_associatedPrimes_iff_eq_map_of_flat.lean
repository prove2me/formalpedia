-- Prove2me | Theorems.Thm_GlobalTheory_mem_associatedPrimes_iff_eq_map_of_flat
-- name    : GlobalTheory.mem_associatedPrimes_iff_eq_map_of_flat
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:11:31.90731+00:00
-- url     : https://prove2.me/theorems/c5a598bd-0d36-4e52-82d4-b38b3aeebca2
-- title:
--   Global Theory: mem associated Primes iff eq map of flat
-- statement:
--   The Global Theory construction uses the mem associated Primes iff eq map of flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasicOpenEqZeroOfMemIInfPowSmul.lean#L261-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasicOpenEqZeroOfMemIInfPowSmul.lean#L261-L289

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
variable [Module B M] [IsScalarTower A B M] [Module.Flat A M]
variable [Module.Flat A B]

theorem GlobalTheory.mem_associatedPrimes_iff_eq_map_of_flat [IsNoetherianRing A] (q : Ideal B) [hq : q.IsPrime]
    [NoZeroDivisors ((q.under A).Fiber B)] :
    q ∈ associatedPrimes B B ↔ q.under A ∈ associatedPrimes A A ∧
      q = (q.under A).map (algebraMap A B) := by sorry
