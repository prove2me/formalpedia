-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Glob_not_pow_dvd_different
-- name    : GlobalTheory.CompanionTheory.Glob.not_pow_dvd_different
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:43:49.63449+00:00
-- url     : https://prove2.me/theorems/2391235b-adf6-4ec0-8717-483fb0216489
-- title:
--   Glob: not pow dvd different
-- statement:
--   The Glob construction uses the not pow dvd different property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/PrimePowerNotDvdDifferent.lean#L8-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/PrimePowerNotDvdDifferent.lean#L8-L91

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_TraceIdempotentNotDivisibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_PrimePowerNotDvdDifferent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain nonZeroDivisors
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Glob

theorem GlobalTheory.CompanionTheory.Glob.not_pow_dvd_different (E : Type) [Field E] [NumberField E] (P J : Ideal (𝓞 E)) [P.IsPrime]
    (p k : ℕ) (hp : p.Prime) (hpP : (p : 𝓞 E) ∈ P) (hPJ : ¬ P ∣ J)
    (hspan : Ideal.span {((p : 𝓞 E)) ^ (Module.finrank ℚ E)} = P ^ k * J) :
    ¬ P ^ k ∣ differentIdeal ℤ (𝓞 E) := by sorry
