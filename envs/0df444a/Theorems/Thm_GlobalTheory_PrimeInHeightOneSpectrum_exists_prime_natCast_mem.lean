-- Prove2me | Theorems.Thm_GlobalTheory_PrimeInHeightOneSpectrum_exists_prime_natCast_mem
-- name    : GlobalTheory.PrimeInHeightOneSpectrum.exists_prime_natCast_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:55:43.424255+00:00
-- url     : https://prove2.me/theorems/bd41c02c-6505-48a0-b74f-d6de13b25f03
-- title:
--   Prime In Height One Spectrum: exists prime nat Cast mem
-- statement:
--   The Prime In Height One Spectrum construction uses the exists prime nat Cast mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsPrimeMemHeightOneSpectrum.lean#L5-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsPrimeMemHeightOneSpectrum.lean#L5-L26

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

theorem GlobalTheory.PrimeInHeightOneSpectrum.exists_prime_natCast_mem {R : Type} [CommRing R] (P : Ideal R) [hP : P.IsPrime] :
    ∀ n : ℕ, n ≠ 0 → (n : R) ∈ P → ∃ p : ℕ, Nat.Prime p ∧ (p : R) ∈ P := by sorry
