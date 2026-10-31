-- Prove2me | Theorems.Thm_OAI_Ostmann_sparse_finite_contraction
-- name    : OAI.Ostmann.sparse_finite_contraction
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T06:25:48.613584+00:00
-- url     : https://prove2.me/theorems/a31b973f-3738-4cc7-ae5a-ca17f477e264
-- title:
--   OAI.Ostmann.sparse_finite_contraction: intermediate lemma from OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Ostmann.inverseGoldbach` and `OAI.Ostmann.twoInfiniteSummandsImpossible`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture)*, OpenAI Math Release, September 24, 2026, result family 13, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Ostmann.sparse_finite_contraction` of [lean/OAI/NumberTheory/Ostmann/Characters/SparseFiniteContraction.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Characters/SparseFiniteContraction.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Ostmann`, with `open scoped Classical BigOperators`):
--
--   ```lean
--   theorem sparse_finite_contraction {n : ℕ}
--       (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
--       (S : ∀ i, Finset (ZMod (p i)))
--       (hS : ∀ i, (S i).Nonempty) (hSp : ∀ i, (S i).card < p i)
--       (hp : ∀ i, (100 : ℝ) ≤ p i)
--       (hlo : ∀ i, (1 / 3 : ℝ) ≤ residueDensity (S i))
--       (hhi : ∀ i, residueDensity (S i) ≤ 2 / 3)
--       (ε : ℝ) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000)
--       (hL1 : ∀ i, (p i : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform (S i) b‖ ≤ ε ^ 2)
--       (L : ℝ) (hL : 1 ≤ L) (hH : (∑ i, (p i : ℝ)⁻¹) ≤ L)
--       (K : ℕ) (hK : 1000 * L ≤ K) :
--       let U := ∏ i, sparseKernelUnitFactor (p i)
--         (((largeTransformSpectrum (normalizedResidueTransform (S i))).card : ℝ) / p i)
--       0 < U ∧ U / 2 ≤ tensorRealUnitMean p (sparseSubsetWeight p S K) ∧
--         ‖finiteKernelOperator (truncatedSparseTensorKernel p S K)‖ ≤
--           2 * U * Real.exp (-(8 / 5) * ∑ i, (p i : ℝ)⁻¹)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Ostmann.residueDensity` (definitions bundle `OAIQ095D001` of this split); `OAI.Ostmann.finiteKernelOperator`, `OAI.Ostmann.largeTransformSpectrum` and `OAI.Ostmann.sparseKernelUnitFactor` (definitions bundle `OAIQ095D002` of this split); `OAI.Ostmann.normalizedResidueTransform` (definitions bundle `OAIQ095D004` of this split); `OAI.Ostmann.tensorRealUnitMean` (definitions bundle `OAIQ095D005` of this split); `OAI.Ostmann.sparseSubsetWeight` and `OAI.Ostmann.truncatedSparseTensorKernel` (definitions bundle `OAIQ095D007` of this split).
--
--   **Used by.** The proofs of `OAI.Ostmann.EventuallyPrimeSumset.favorable_tail_prime_mass`, `OAI.Ostmann.EventuallyPrimeSumset.sparse_tail_coverage`, `OAI_Ostmann_EventuallyPrimeSumset_sparse_tail_mass_bound`, `OAI_Ostmann_sparseWeightedPrimeSum_lower` and `OAI_Ostmann_sparse_pair_coverage_size_bound` of this split import it.
-- source:
--   OpenAI, The additive indecomposability of the primes (Ostmann's inverse Goldbach conjecture), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 13; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/the-additive-indecomposability-of-the-primes-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/Ostmann/Characters/SparseFiniteContraction.lean (declaration OAI.Ostmann.sparse_finite_contraction)

import Mathlib
import Definitions.Def_OAIQ095D007

section

attribute [-instance] _root_.BernoulliRegular.instNeZeroNatHSubOfNat_solutions _root_.OAI.LargePrimeGaps.finiteSetoidFintype _root_.OAI.Ostmann.finalParityReassignmentsFintype _root_.OAI.Ostmann.finite_primeLogAtom _root_.OAI.Ostmann.quartetProductFiberFintype _root_.OAI.Ostmann.treeLeafFiberFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Ostmann
open scoped Classical BigOperators

theorem sparse_finite_contraction {n : ℕ}
    (p : Fin n → ℕ) [∀ i, Fact (p i).Prime]
    (S : ∀ i, Finset (ZMod (p i)))
    (hS : ∀ i, (S i).Nonempty) (hSp : ∀ i, (S i).card < p i)
    (hp : ∀ i, (100 : ℝ) ≤ p i)
    (hlo : ∀ i, (1 / 3 : ℝ) ≤ residueDensity (S i))
    (hhi : ∀ i, residueDensity (S i) ≤ 2 / 3)
    (ε : ℝ) (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 1000000)
    (hL1 : ∀ i, (p i : ℝ)⁻¹ * ∑ b, ‖normalizedResidueTransform (S i) b‖ ≤ ε ^ 2)
    (L : ℝ) (hL : 1 ≤ L) (hH : (∑ i, (p i : ℝ)⁻¹) ≤ L)
    (K : ℕ) (hK : 1000 * L ≤ K) :
    let U := ∏ i, sparseKernelUnitFactor (p i)
      (((largeTransformSpectrum (normalizedResidueTransform (S i))).card : ℝ) / p i)
    0 < U ∧ U / 2 ≤ tensorRealUnitMean p (sparseSubsetWeight p S K) ∧
      ‖finiteKernelOperator (truncatedSparseTensorKernel p S K)‖ ≤
        2 * U * Real.exp (-(8 / 5) * ∑ i, (p i : ℝ)⁻¹) := by
  sorry

end Ostmann

end OAI
end
