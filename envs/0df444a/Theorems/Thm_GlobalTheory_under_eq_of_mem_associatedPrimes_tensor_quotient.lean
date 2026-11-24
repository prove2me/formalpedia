-- Prove2me | Theorems.Thm_GlobalTheory_under_eq_of_mem_associatedPrimes_tensor_quotient
-- name    : GlobalTheory.under_eq_of_mem_associatedPrimes_tensor_quotient
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:24:48.963417+00:00
-- url     : https://prove2.me/theorems/140f9377-8851-4bfb-84d7-4387c448248a
-- title:
--   Global Theory: under eq of mem associated Primes tensor quotient
-- statement:
--   The Global Theory construction uses the under eq of mem associated Primes tensor quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasicOpenEqZeroOfMemIInfPowSmul.lean#L91-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasicOpenEqZeroOfMemIInfPowSmul.lean#L91-L116

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

theorem GlobalTheory.under_eq_of_mem_associatedPrimes_tensor_quotient (p : Ideal A) [hp : p.IsPrime]
    {q : Ideal B} (hq : q ∈ associatedPrimes B (M ⊗[A] (A ⧸ p))) : q.under A = p := by sorry
