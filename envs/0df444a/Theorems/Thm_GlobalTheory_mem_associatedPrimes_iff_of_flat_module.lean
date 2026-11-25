-- Prove2me | Theorems.Thm_GlobalTheory_mem_associatedPrimes_iff_of_flat_module
-- name    : GlobalTheory.mem_associatedPrimes_iff_of_flat_module
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:11:35.067386+00:00
-- url     : https://prove2.me/theorems/d22d971e-f861-45b4-9a0d-a8b305b7c2db
-- title:
--   Global Theory: mem associated Primes iff of flat module
-- statement:
--   The Global Theory construction uses the mem associated Primes iff of flat module property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasicOpenEqZeroOfMemIInfPowSmul.lean#L183-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasicOpenEqZeroOfMemIInfPowSmul.lean#L183-L198

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

theorem GlobalTheory.mem_associatedPrimes_iff_of_flat_module [IsNoetherianRing A] (q : Ideal B) [q.IsPrime] :
    q ∈ associatedPrimes B M ↔ q.under A ∈ associatedPrimes A A ∧
      q ∈ associatedPrimes B (M ⊗[A] (q.under A).ResidueField) := by sorry
