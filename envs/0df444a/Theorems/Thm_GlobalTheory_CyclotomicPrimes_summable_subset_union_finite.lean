-- Prove2me | Theorems.Thm_GlobalTheory_CyclotomicPrimes_summable_subset_union_finite
-- name    : GlobalTheory.CyclotomicPrimes.summable_subset_union_finite
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:34:51.901173+00:00
-- url     : https://prove2.me/theorems/c9d88cd9-86ec-4c1b-b48e-c277b3b047cb
-- title:
--   Cyclotomic Primes: summable subset union finite
-- statement:
--   The Cyclotomic Primes construction uses the summable subset union finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsPrimeAbsNormEqOfIrreducibleCyclotomic.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsPrimeAbsNormEqOfIrreducibleCyclotomic.lean#L13-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdealCharacterLContinuationNeZeroOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SummableInvAbsNormPrimesOfNotPrimeNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsContinuousNormCharLFunctionNeZeroOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPrimeNormCyclotomicCharNeOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DedekindZetaEulerProductMulSubOneEntireNeZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPrimeAbsNormEqOfIrreducibleCyclotomic
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
open GlobalTheory GlobalTheory.CyclotomicPrimes

theorem GlobalTheory.CyclotomicPrimes.summable_subset_union_finite {ι : Type} (f : ι → ℝ) (A B C : Set ι) (hB : B.Finite) (h : C ⊆ A ∪ B)
    (hA : Summable fun x : A => f x) : Summable fun x : C => f x := by sorry
