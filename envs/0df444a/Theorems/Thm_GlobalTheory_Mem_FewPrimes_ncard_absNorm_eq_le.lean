-- Prove2me | Theorems.Thm_GlobalTheory_Mem_FewPrimes_ncard_absNorm_eq_le
-- name    : GlobalTheory.Mem.FewPrimes.ncard_absNorm_eq_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:23:05.252728+00:00
-- url     : https://prove2.me/theorems/004a1986-dd81-4eab-a77c-245655306fdb
-- title:
--   Few Primes: ncard abs Norm eq le
-- statement:
--   The Few Primes construction uses the ncard abs Norm eq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PrimeIdealsCountingBounds.lean#L86-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PrimeIdealsCountingBounds.lean#L86-L101

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

theorem GlobalTheory.Mem.FewPrimes.ncard_absNorm_eq_le (hK : Module.finrank ℚ K = 2) (p : ℕ) (hp : p.Prime) :
    {v : HeightOneSpectrum (𝓞 K) | Ideal.absNorm v.asIdeal = p}.ncard ≤ 2 := by sorry
