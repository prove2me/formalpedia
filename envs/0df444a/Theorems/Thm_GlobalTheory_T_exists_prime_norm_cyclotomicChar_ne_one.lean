-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_prime_norm_cyclotomicChar_ne_one
-- name    : GlobalTheory.T.exists_prime_norm_cyclotomicChar_ne_one
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:40:30.065568+00:00
-- url     : https://prove2.me/theorems/66cf359a-5f5c-4a0b-95c6-9c2cff09501a
-- title:
--   T: exists prime norm cyclotomic Char ne one
-- statement:
--   The T construction uses the exists prime norm cyclotomic Char ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsPrimeNormCyclotomicCharNeOneStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsPrimeNormCyclotomicCharNeOneStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPrimeNormCyclotomicCharNeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdealCharacterLContinuationNeZeroOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPrimeNormCyclotomicCharNeOneStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_prime_norm_cyclotomicChar_ne_one : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ), m.Prime → Irreducible (cyclotomic m K) → ∀ χ : (ZMod m)ˣ →* ℂˣ, χ ≠ 1 → ∃ (P : HeightOneSpectrum (𝓞 K)) (u : (ZMod m)ˣ), (u : ZMod m) = (Ideal.absNorm P.asIdeal : ℕ) ∧ χ u ≠ 1 := by sorry
