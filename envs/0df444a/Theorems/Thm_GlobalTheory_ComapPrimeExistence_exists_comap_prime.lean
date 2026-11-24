-- Prove2me | Theorems.Thm_GlobalTheory_ComapPrimeExistence_exists_comap_prime
-- name    : GlobalTheory.ComapPrimeExistence.exists_comap_prime
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:14:56.258962+00:00
-- url     : https://prove2.me/theorems/ed9eba75-57e0-489e-b659-47c75c407af5
-- title:
--   Comap Prime Existence: exists comap prime
-- statement:
--   The Comap Prime Existence construction uses the exists comap prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsComapPrime.lean#L7-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ExistsComapPrime.lean#L7-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsComapPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ComapPrimeExistence
open NumberField IsDedekindDomain

theorem GlobalTheory.ComapPrimeExistence.exists_comap_prime {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (φ : E →+* K) (w : HeightOneSpectrum (RingOfIntegers K)) :
    ∃ Q : HeightOneSpectrum (RingOfIntegers E), ∀ r : RingOfIntegers E,
      r ∈ Q.asIdeal ↔ (RingOfIntegers.mapRingHom φ : RingOfIntegers E → RingOfIntegers K) r ∈ w.asIdeal := by sorry
