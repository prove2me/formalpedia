-- Prove2me | Theorems.Thm_GlobalTheory_T_prime_power_not_dvd_different
-- name    : GlobalTheory.T.prime_power_not_dvd_different
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:54:39.086393+00:00
-- url     : https://prove2.me/theorems/d26fdaee-69d5-4f68-af22-39c10aafc2dc
-- title:
--   T: prime power not dvd different
-- statement:
--   The T construction uses the prime power not dvd different property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/PrimePowerNotDvdDifferentStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/PrimePowerNotDvdDifferentStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_PrimePowerNotDvdDifferent
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_PrimePowerNotDvdDifferentStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.prime_power_not_dvd_different : ∀ (E : Type) [Field E] [NumberField E] (P J : Ideal (𝓞 E)) [P.IsPrime] (p k : ℕ), p.Prime → (p : 𝓞 E) ∈ P → ¬ P ∣ J → Ideal.span {((p : 𝓞 E)) ^ (Module.finrank ℚ E)} = P ^ k * J → ¬ P ^ k ∣ differentIdeal ℤ (𝓞 E) := by sorry
