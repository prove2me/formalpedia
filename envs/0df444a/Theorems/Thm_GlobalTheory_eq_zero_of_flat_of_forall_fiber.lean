-- Prove2me | Theorems.Thm_GlobalTheory_eq_zero_of_flat_of_forall_fiber
-- name    : GlobalTheory.eq_zero_of_flat_of_forall_fiber
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:51:18.185048+00:00
-- url     : https://prove2.me/theorems/91bd8fc8-9e72-4cf2-8eff-8a17036d7e8e
-- title:
--   Global Theory: eq zero of flat of forall fiber
-- statement:
--   The Global Theory construction uses the eq zero of flat of forall fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasicOpenEqZeroOfMemIInfPowSmul.lean#L313-L328
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasicOpenEqZeroOfMemIInfPowSmul.lean#L313-L328

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

theorem GlobalTheory.eq_zero_of_flat_of_forall_fiber [IsNoetherianRing A] [IsNoetherianRing B]
    {L : Type*} [AddCommGroup L] [Module B L] [Module.Flat B L]
    (hfib : ∀ p : PrimeSpectrum A, p.asIdeal ∈ associatedPrimes A A →
      NoZeroDivisors (p.asIdeal.Fiber B)) {x : L}
    (hx : ∀ q : PrimeSpectrum B, q.asIdeal.under A ∈ associatedPrimes A A →
      ∃ q' : PrimeSpectrum B, q'.asIdeal.under A = q.asIdeal.under A ∧
        (LocalizedModule.mk x 1 : LocalizedModule q'.asIdeal.primeCompl L) = 0) : x = 0 := by sorry
