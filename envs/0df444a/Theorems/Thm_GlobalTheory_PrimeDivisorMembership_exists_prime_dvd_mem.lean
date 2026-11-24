-- Prove2me | Theorems.Thm_GlobalTheory_PrimeDivisorMembership_exists_prime_dvd_mem
-- name    : GlobalTheory.PrimeDivisorMembership.exists_prime_dvd_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:53:47.97084+00:00
-- url     : https://prove2.me/theorems/520e292d-d4a6-4c22-9da5-1d3a6e486643
-- title:
--   Prime Divisor Membership: exists prime dvd mem
-- statement:
--   The Prime Divisor Membership construction uses the exists prime dvd mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsPrimeDvdMem.lean#L7-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsPrimeDvdMem.lean#L7-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsPrimeDvdMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open GlobalTheory GlobalTheory.PrimeDivisorMembership

theorem GlobalTheory.PrimeDivisorMembership.exists_prime_dvd_mem : ∀ {R : Type u_1} [inst : CommRing R] (P : Ideal R), Ideal.IsPrime P → ∀ (n : ℕ), n ≠ (0 : ℕ) → (↑n : R) ∈ P → ∃ (q : ℕ), Nat.Prime q ∧ q ∣ n ∧ (↑q : R) ∈ P := by sorry
