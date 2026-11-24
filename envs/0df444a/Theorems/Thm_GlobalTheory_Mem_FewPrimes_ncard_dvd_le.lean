-- Prove2me | Theorems.Thm_GlobalTheory_Mem_FewPrimes_ncard_dvd_le
-- name    : GlobalTheory.Mem.FewPrimes.ncard_dvd_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:23:27.417996+00:00
-- url     : https://prove2.me/theorems/c7bd67ef-07a6-4830-af16-0239c079b62e
-- title:
--   Few Primes: ncard dvd le
-- statement:
--   The Few Primes construction uses the ncard dvd le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PrimeIdealsCountingBounds.lean#L103-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PrimeIdealsCountingBounds.lean#L103-L123

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

theorem GlobalTheory.Mem.FewPrimes.ncard_dvd_le (𝔮 : Ideal (𝓞 K)) (hq : 𝔮 ≠ ⊥) :
    ({v : HeightOneSpectrum (𝓞 K) | v.asIdeal ∣ 𝔮}.ncard : ℝ) ≤
      3 * Real.log (4 * Ideal.absNorm 𝔮) := by sorry
