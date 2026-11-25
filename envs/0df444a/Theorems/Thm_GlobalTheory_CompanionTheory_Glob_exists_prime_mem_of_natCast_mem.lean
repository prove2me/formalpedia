-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Glob_exists_prime_mem_of_natCast_mem
-- name    : GlobalTheory.CompanionTheory.Glob.exists_prime_mem_of_natCast_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:43:37.683803+00:00
-- url     : https://prove2.me/theorems/b86d6868-7c3e-42ea-8447-d6d67560f5b3
-- title:
--   Glob: exists prime mem of nat Cast mem
-- statement:
--   The Glob construction uses the exists prime mem of nat Cast mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DifferentDvdRamifiedPrimePower.lean#L9-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DifferentDvdRamifiedPrimePower.lean#L9-L11

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_PrimePowerNotDvdDifferentStatement
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTer
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DifferentDvdRamifiedPrimePower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Glob

theorem GlobalTheory.CompanionTheory.Glob.exists_prime_mem_of_natCast_mem {R : Type*} [CommRing R] (P : Ideal R) [hP : P.IsPrime]
    (t : ℕ) (ht : t ≠ 0) (htP : (t : R) ∈ P) : ∃ p : ℕ, p.Prime ∧ p ∣ t ∧ (p : R) ∈ P := by sorry
