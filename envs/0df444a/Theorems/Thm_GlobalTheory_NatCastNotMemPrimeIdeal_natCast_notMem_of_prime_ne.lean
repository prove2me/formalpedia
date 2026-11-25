-- Prove2me | Theorems.Thm_GlobalTheory_NatCastNotMemPrimeIdeal_natCast_notMem_of_prime_ne
-- name    : GlobalTheory.NatCastNotMemPrimeIdeal.natCast_notMem_of_prime_ne
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:14:48.302409+00:00
-- url     : https://prove2.me/theorems/67680739-677c-4cbb-8324-72ca18a3a64f
-- title:
--   Nat Cast Not Mem Prime Ideal: nat Cast not Mem of prime ne
-- statement:
--   The Nat Cast Not Mem Prime Ideal construction uses the nat Cast not Mem of prime ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NatCastNotMemOfPrimeNe.lean#L5-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NatCastNotMemOfPrimeNe.lean#L5-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NatCastNotMemOfPrimeNe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NatCastNotMemPrimeIdeal

theorem GlobalTheory.NatCastNotMemPrimeIdeal.natCast_notMem_of_prime_ne {L : Type} [Field L] [NumberField L]
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hne : q ≠ p)
    (hqw : (q : NumberField.RingOfIntegers L) ∈ w.asIdeal) :
    (p : NumberField.RingOfIntegers L) ∉ w.asIdeal := by sorry
