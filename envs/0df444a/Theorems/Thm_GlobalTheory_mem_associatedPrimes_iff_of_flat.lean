-- Prove2me | Theorems.Thm_GlobalTheory_mem_associatedPrimes_iff_of_flat
-- name    : GlobalTheory.mem_associatedPrimes_iff_of_flat
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:52:37.454805+00:00
-- url     : https://prove2.me/theorems/6ec12aa5-bf35-437f-b75e-a8570357a306
-- title:
--   Global Theory: mem associated Primes iff of flat
-- statement:
--   The Global Theory construction uses the mem associated Primes iff of flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasicOpenEqZeroOfMemIInfPowSmul.lean#L243-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasicOpenEqZeroOfMemIInfPowSmul.lean#L243-L248

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

theorem GlobalTheory.mem_associatedPrimes_iff_of_flat [IsNoetherianRing A] (q : Ideal B) [q.IsPrime] :
    q ∈ associatedPrimes B B ↔ q.under A ∈ associatedPrimes A A ∧
      ∃ Q ∈ associatedPrimes ((q.under A).Fiber B) ((q.under A).Fiber B),
        Q.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] (q.under A).Fiber B) = q := by sorry
