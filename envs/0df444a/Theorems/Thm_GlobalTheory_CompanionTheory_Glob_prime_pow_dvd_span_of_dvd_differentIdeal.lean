-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Glob_prime_pow_dvd_span_of_dvd_differentIdeal
-- name    : GlobalTheory.CompanionTheory.Glob.prime_pow_dvd_span_of_dvd_differentIdeal
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:44:21.711992+00:00
-- url     : https://prove2.me/theorems/321355b7-b57d-4c20-a158-9367c8d7a4e4
-- title:
--   Glob: prime pow dvd span of dvd different Ideal
-- statement:
--   The Glob construction uses the prime pow dvd span of dvd different Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DifferentDvdRamifiedPrimePower.lean#L13-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DifferentDvdRamifiedPrimePower.lean#L13-L39

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

theorem GlobalTheory.CompanionTheory.Glob.prime_pow_dvd_span_of_dvd_differentIdeal (E : Type) [Field E] [NumberField E] (t : ℕ)
    (ht : t ≠ 0)
    (h : ∀ P : Ideal (𝓞 E), P.IsPrime → P ≠ ⊥ → P ∣ differentIdeal ℤ (𝓞 E) → (t : 𝓞 E) ∈ P)
    (P : Ideal (𝓞 E)) (hPp : Prime P) (i : ℕ) (hi : P ^ i ∣ differentIdeal ℤ (𝓞 E)) :
    P ^ i ∣ Ideal.span {((t : 𝓞 E)) ^ (Module.finrank ℚ E)} := by sorry
