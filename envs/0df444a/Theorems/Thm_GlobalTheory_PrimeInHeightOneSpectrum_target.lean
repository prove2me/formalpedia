-- Prove2me | Theorems.Thm_GlobalTheory_PrimeInHeightOneSpectrum_target
-- name    : GlobalTheory.PrimeInHeightOneSpectrum.target
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:55:56.835741+00:00
-- url     : https://prove2.me/theorems/a953278f-669a-4e6a-9bfc-8c384ff9beb7
-- title:
--   Prime In Height One Spectrum: target
-- statement:
--   The Prime In Height One Spectrum construction uses the target property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsPrimeMemHeightOneSpectrum.lean#L36-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsPrimeMemHeightOneSpectrum.lean#L36-L40

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

theorem GlobalTheory.PrimeInHeightOneSpectrum.target : ∀ {K : Type} [inst : Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)),
    ∃ (p : ℕ), Nat.Prime p ∧ (↑p : NumberField.RingOfIntegers K) ∈
      IsDedekindDomain.HeightOneSpectrum.asIdeal v := by sorry
