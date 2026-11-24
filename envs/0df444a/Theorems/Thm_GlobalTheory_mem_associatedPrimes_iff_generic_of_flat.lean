-- Prove2me | Theorems.Thm_GlobalTheory_mem_associatedPrimes_iff_generic_of_flat
-- name    : GlobalTheory.mem_associatedPrimes_iff_generic_of_flat
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:11:24.115804+00:00
-- url     : https://prove2.me/theorems/a4ce93c0-ad3f-4ba8-8b8d-79da796410bc
-- title:
--   Global Theory: mem associated Primes iff generic of flat
-- statement:
--   The Global Theory construction uses the mem associated Primes iff generic of flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasicOpenEqZeroOfMemIInfPowSmul.lean#L291-L311
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasicOpenEqZeroOfMemIInfPowSmul.lean#L291-L311

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

theorem GlobalTheory.mem_associatedPrimes_iff_generic_of_flat [IsNoetherianRing A] (q : Ideal B)
    [hq : q.IsPrime] [NoZeroDivisors ((q.under A).Fiber B)] :
    q ∈ associatedPrimes B B ↔ q.under A ∈ associatedPrimes A A ∧
      ∀ q' : Ideal B, q'.IsPrime → q'.under A = q.under A → q ≤ q' := by sorry
