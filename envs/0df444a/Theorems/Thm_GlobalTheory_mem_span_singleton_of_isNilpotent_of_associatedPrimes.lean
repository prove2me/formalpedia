-- Prove2me | Theorems.Thm_GlobalTheory_mem_span_singleton_of_isNilpotent_of_associatedPrimes
-- name    : GlobalTheory.mem_span_singleton_of_isNilpotent_of_associatedPrimes
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:11:08.310863+00:00
-- url     : https://prove2.me/theorems/71867c55-e948-45bd-bbce-1514be9d91f4
-- title:
--   Global Theory: mem span singleton of is Nilpotent of associated Primes
-- statement:
--   The Global Theory construction uses the mem span singleton of is Nilpotent of associated Primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsReducedOfNonZeroDivisorMemJacobsonOfAssociated.lean#L7-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsReducedOfNonZeroDivisorMemJacobsonOfAssociated.lean#L7-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsReducedOfNonZeroDivisorMemJacobsonOfAssociated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory

theorem GlobalTheory.mem_span_singleton_of_isNilpotent_of_associatedPrimes {R : Type} [CommRing R]
    [IsNoetherianRing R] (x : R)
    (hP : ∀ (P : Ideal R) [P.IsPrime], P ∈ associatedPrimes R (R ⧸ Ideal.span {x}) →
      IsDomain (Localization.AtPrime P))
    {n : R} (hn : IsNilpotent n) : n ∈ Ideal.span {x} := by sorry
