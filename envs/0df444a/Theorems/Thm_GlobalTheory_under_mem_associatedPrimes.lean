-- Prove2me | Theorems.Thm_GlobalTheory_under_mem_associatedPrimes
-- name    : GlobalTheory.under_mem_associatedPrimes
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:54:44.471021+00:00
-- url     : https://prove2.me/theorems/12143d21-66e8-4553-aab1-7e804623d15f
-- title:
--   Global Theory: under mem associated Primes
-- statement:
--   The Global Theory construction uses the under mem associated Primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasicOpenEqZeroOfMemIInfPowSmul.lean#L47-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasicOpenEqZeroOfMemIInfPowSmul.lean#L47-L54

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

theorem GlobalTheory.under_mem_associatedPrimes [Module B M] [IsScalarTower A B M] {q : Ideal B}
    (hq : q ∈ associatedPrimes B M) : q.under A ∈ associatedPrimes A M := by sorry
