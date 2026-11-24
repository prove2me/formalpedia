-- Prove2me | Theorems.Thm_GlobalTheory_mem_associatedPrimes_tensor_residueField_iff
-- name    : GlobalTheory.mem_associatedPrimes_tensor_residueField_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:11:38.466831+00:00
-- url     : https://prove2.me/theorems/f2d8cbad-d905-4c9c-a2ad-4e77405094bb
-- title:
--   Global Theory: mem associated Primes tensor residue Field iff
-- statement:
--   The Global Theory construction uses the mem associated Primes tensor residue Field iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasicOpenEqZeroOfMemIInfPowSmul.lean#L200-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasicOpenEqZeroOfMemIInfPowSmul.lean#L200-L239

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

theorem GlobalTheory.mem_associatedPrimes_tensor_residueField_iff (p : Ideal A) [p.IsPrime] (q : Ideal B) :
    q ∈ associatedPrimes B (B ⊗[A] p.ResidueField) ↔
      ∃ Q ∈ associatedPrimes (p.Fiber B) (p.Fiber B),
        Q.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] p.Fiber B) = q := by sorry
