-- Prove2me | Theorems.Thm_GlobalTheory_PrimeInHeightOneSpectrum_exists_prime_mem_heightOneSpectrum
-- name    : GlobalTheory.PrimeInHeightOneSpectrum.exists_prime_mem_heightOneSpectrum
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:55:38.792862+00:00
-- url     : https://prove2.me/theorems/03e1c04c-26ac-4918-9e67-2968a6775f22
-- title:
--   Prime In Height One Spectrum: exists prime mem height One Spectrum
-- statement:
--   The Prime In Height One Spectrum construction uses the exists prime mem height One Spectrum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsPrimeMemHeightOneSpectrum.lean#L28-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsPrimeMemHeightOneSpectrum.lean#L28-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPrimeMemHeightOneSpectrum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PrimeInHeightOneSpectrum

theorem GlobalTheory.PrimeInHeightOneSpectrum.exists_prime_mem_heightOneSpectrum {K : Type} [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ∃ (p : ℕ), Nat.Prime p ∧ (↑p : NumberField.RingOfIntegers K) ∈
      IsDedekindDomain.HeightOneSpectrum.asIdeal v := by sorry
