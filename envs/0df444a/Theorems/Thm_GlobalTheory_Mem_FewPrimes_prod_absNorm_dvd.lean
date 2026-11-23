-- Prove2me | Theorems.Thm_GlobalTheory_Mem_FewPrimes_prod_absNorm_dvd
-- name    : GlobalTheory.Mem.FewPrimes.prod_absNorm_dvd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:24.886847+00:00
-- url     : https://prove2.me/theorems/6484759e-b140-4223-8458-e304bbfd48ba
-- title:
--   Few Primes: prod abs Norm dvd
-- statement:
--   The Few Primes construction uses the prod abs Norm dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PrimeIdealsCountingBounds.lean#L10-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PrimeIdealsCountingBounds.lean#L10-L17

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

theorem GlobalTheory.Mem.FewPrimes.prod_absNorm_dvd (s : Finset (HeightOneSpectrum (𝓞 K))) (I : Ideal (𝓞 K))
    (h : ∀ v ∈ s, v.asIdeal ∣ I) :
    ∏ v ∈ s, Ideal.absNorm v.asIdeal ∣ Ideal.absNorm I := by sorry
