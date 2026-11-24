-- Prove2me | Theorems.Thm_GlobalTheory_mem_associatedPrimes_tensor_quotient_under
-- name    : GlobalTheory.mem_associatedPrimes_tensor_quotient_under
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:24.923969+00:00
-- url     : https://prove2.me/theorems/9d1cc8d4-7af9-411c-b86c-75b6822d6878
-- title:
--   Global Theory: mem associated Primes tensor quotient under
-- statement:
--   The Global Theory construction uses the mem associated Primes tensor quotient under property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasicOpenEqZeroOfMemIInfPowSmul.lean#L118-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasicOpenEqZeroOfMemIInfPowSmul.lean#L118-L133

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

theorem GlobalTheory.mem_associatedPrimes_tensor_quotient_under [IsNoetherianRing A] {N : Type*}
    [AddCommGroup N] [Module A N] [hN : Module.Finite A N] {q : Ideal B}
    (hq : q ∈ associatedPrimes B (M ⊗[A] N)) :
    q ∈ associatedPrimes B (M ⊗[A] (A ⧸ q.under A)) := by sorry
