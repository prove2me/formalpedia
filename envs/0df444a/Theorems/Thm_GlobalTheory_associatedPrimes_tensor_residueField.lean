-- Prove2me | Theorems.Thm_GlobalTheory_associatedPrimes_tensor_residueField
-- name    : GlobalTheory.associatedPrimes_tensor_residueField
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:06:31.456849+00:00
-- url     : https://prove2.me/theorems/b6bb0a62-2dfe-4a19-888c-08ae3579b2b4
-- title:
--   Global Theory: associated Primes tensor residue Field
-- statement:
--   The Global Theory construction uses the associated Primes tensor residue Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasicOpenEqZeroOfMemIInfPowSmul.lean#L141-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasicOpenEqZeroOfMemIInfPowSmul.lean#L141-L181

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

theorem GlobalTheory.associatedPrimes_tensor_residueField (p : Ideal A) [hp : p.IsPrime] :
    associatedPrimes B (M ⊗[A] p.ResidueField) = associatedPrimes B (M ⊗[A] (A ⧸ p)) := by sorry
