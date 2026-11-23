-- Prove2me | Theorems.Thm_GlobalTheory_Mem_FewPrimes_finite_absNorm_le
-- name    : GlobalTheory.Mem.FewPrimes.finite_absNorm_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:32.324673+00:00
-- url     : https://prove2.me/theorems/aca5239f-26c7-4497-9681-e4459f7bb74e
-- title:
--   Few Primes: finite abs Norm le
-- statement:
--   The Few Primes construction uses the finite abs Norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PrimeIdealsCountingBounds.lean#L19-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PrimeIdealsCountingBounds.lean#L19-L26

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

theorem GlobalTheory.Mem.FewPrimes.finite_absNorm_le (X : ℝ) :
    {v : HeightOneSpectrum (𝓞 K) | (Ideal.absNorm v.asIdeal : ℝ) ≤ X}.Finite := by sorry
