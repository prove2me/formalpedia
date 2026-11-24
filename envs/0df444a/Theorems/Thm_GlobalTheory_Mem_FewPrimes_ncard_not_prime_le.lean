-- Prove2me | Theorems.Thm_GlobalTheory_Mem_FewPrimes_ncard_not_prime_le
-- name    : GlobalTheory.Mem.FewPrimes.ncard_not_prime_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:22:50.831947+00:00
-- url     : https://prove2.me/theorems/b29c8b14-6348-46d1-9c7c-47559c78b418
-- title:
--   Few Primes: ncard not prime le
-- statement:
--   The Few Primes construction uses the ncard not prime le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PrimeIdealsCountingBounds.lean#L62-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PrimeIdealsCountingBounds.lean#L62-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPrimeMemHeightOneSpectrum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PrimeIdealsCountingBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.FewPrimes
variable {K : Type} [Field K] [NumberField K]

theorem GlobalTheory.Mem.FewPrimes.ncard_not_prime_le (hK : Module.finrank ℚ K = 2) (X : ℝ) :
    ({v : HeightOneSpectrum (𝓞 K) | (Ideal.absNorm v.asIdeal : ℝ) ≤ X ∧
      ¬ (Ideal.absNorm v.asIdeal).Prime}.ncard : ℝ) ≤ Real.sqrt X := by sorry
