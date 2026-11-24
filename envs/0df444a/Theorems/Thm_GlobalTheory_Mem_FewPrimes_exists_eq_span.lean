-- Prove2me | Theorems.Thm_GlobalTheory_Mem_FewPrimes_exists_eq_span
-- name    : GlobalTheory.Mem.FewPrimes.exists_eq_span
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:23:37.226656+00:00
-- url     : https://prove2.me/theorems/77460abe-7354-4ac7-be32-7bc2d7c5f4ff
-- title:
--   Few Primes: exists eq span
-- statement:
--   The Few Primes construction uses the exists eq span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PrimeIdealsCountingBounds.lean#L38-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PrimeIdealsCountingBounds.lean#L38-L60

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

theorem GlobalTheory.Mem.FewPrimes.exists_eq_span (hK : Module.finrank ℚ K = 2) (v : HeightOneSpectrum (𝓞 K))
    (hv : ¬ (Ideal.absNorm v.asIdeal).Prime) :
    ∃ p : ℕ, p.Prime ∧ v.asIdeal = Ideal.span {(p : 𝓞 K)} ∧ Ideal.absNorm v.asIdeal = p ^ 2 := by sorry
